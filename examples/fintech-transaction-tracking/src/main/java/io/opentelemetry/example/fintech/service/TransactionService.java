package io.opentelemetry.example.fintech.service;

import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.StatusCode;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Scope;
import io.opentelemetry.example.fintech.model.Transaction;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * Transaction Service
 * 
 * Core business logic for transaction processing with comprehensive
 * OpenTelemetry instrumentation.
 */
@Service
public class TransactionService {

    @Autowired
    private Tracer tracer;

    @Autowired
    private RiskAssessmentService riskAssessmentService;

    @Autowired
    private FraudDetectionService fraudDetectionService;

    @Autowired
    private ComplianceService complianceService;

    // In-memory storage for demo (use database in production)
    private final Map<String, Transaction> transactionStore = new ConcurrentHashMap<>();

    /**
     * Process a financial transaction
     */
    public Transaction processTransaction(Transaction transaction) {
        Span span = tracer.spanBuilder("transaction.process")
                .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            // Add transaction attributes
            span.setAttribute("fintech.transaction.id", transaction.getTransactionId());
            span.setAttribute("fintech.transaction.type", transaction.getType().toString());
            span.setAttribute("fintech.transaction.amount", transaction.getAmount().doubleValue());
            span.setAttribute("fintech.transaction.currency", transaction.getCurrency());
            span.setAttribute("fintech.transaction.is_high_value", transaction.isHighValue());
            span.setAttribute("fintech.transaction.is_cross_border", transaction.isCrossBorder());
            
            // Record event: Transaction received
            span.addEvent("transaction_received");
            
            // Step 1: Compliance check
            complianceService.performComplianceCheck(transaction);
            
            // Step 2: Risk assessment
            riskAssessmentService.assessRisk(transaction);
            
            // Step 3: Fraud detection
            fraudDetectionService.detectFraud(transaction);
            
            // Step 4: Determine transaction status based on checks
            determineTransactionStatus(transaction);
            
            // Step 5: Store transaction
            transactionStore.put(transaction.getTransactionId(), transaction);
            
            // Record event: Transaction processed
            span.addEvent("transaction_completed", io.opentelemetry.api.common.Attributes.builder()
                    .put("fintech.transaction.status", transaction.getStatus().toString())
                    .put("fintech.risk.level", transaction.getRiskLevel().toString())
                    .build());
            
            span.setStatus(StatusCode.OK);
            return transaction;
            
        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR, "Transaction processing failed");
            transaction.setStatus(Transaction.TransactionStatus.FAILED);
            throw new RuntimeException("Transaction processing failed", e);
            
        } finally {
            span.end();
        }
    }

    /**
     * Get transaction by ID
     */
    public Transaction getTransaction(String transactionId) {
        Span span = tracer.spanBuilder("transaction.get")
                .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            span.setAttribute("fintech.transaction.id", transactionId);
            
            Transaction transaction = transactionStore.get(transactionId);
            
            if (transaction != null) {
                span.setAttribute("fintech.transaction.found", true);
                span.setStatus(StatusCode.OK);
            } else {
                span.setAttribute("fintech.transaction.found", false);
                span.setStatus(StatusCode.ERROR, "Transaction not found");
            }
            
            return transaction;
            
        } finally {
            span.end();
        }
    }

    /**
     * Determine final transaction status based on all checks
     */
    private void determineTransactionStatus(Transaction transaction) {
        if (transaction.isFraudDetected()) {
            transaction.setStatus(Transaction.TransactionStatus.FLAGGED_FOR_REVIEW);
        } else if (transaction.getRiskLevel() == Transaction.RiskLevel.CRITICAL) {
            transaction.setStatus(Transaction.TransactionStatus.DECLINED);
        } else if (transaction.getRiskLevel() == Transaction.RiskLevel.HIGH) {
            transaction.setStatus(Transaction.TransactionStatus.FLAGGED_FOR_REVIEW);
        } else if (transaction.requiresManualReview()) {
            transaction.setStatus(Transaction.TransactionStatus.FLAGGED_FOR_REVIEW);
        } else {
            transaction.setStatus(Transaction.TransactionStatus.COMPLETED);
        }
    }
}

