package io.opentelemetry.example.fintech.controller;

import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.StatusCode;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Scope;
import io.opentelemetry.example.fintech.model.Transaction;
import io.opentelemetry.example.fintech.service.TransactionService;
import io.opentelemetry.semconv.SemanticAttributes;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.*;

import java.util.HashMap;
import java.util.Map;

/**
 * Transaction Controller
 * 
 * REST API for financial transaction processing with OpenTelemetry instrumentation.
 */
@RestController
@RequestMapping("/api/transactions")
public class TransactionController {

    @Autowired
    private TransactionService transactionService;

    @Autowired
    private Tracer tracer;

    /**
     * Process a new transaction
     * 
     * POST /api/transactions
     */
    @PostMapping
    public ResponseEntity<Map<String, Object>> processTransaction(@RequestBody Transaction transaction) {
        Span span = tracer.spanBuilder("http.server.process_transaction")
                .setSpanKind(io.opentelemetry.api.trace.SpanKind.SERVER)
                .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            // Add standard HTTP semantic conventions
            span.setAttribute(SemanticAttributes.HTTP_METHOD, "POST");
            span.setAttribute(SemanticAttributes.HTTP_ROUTE, "/api/transactions");
            span.setAttribute(SemanticAttributes.HTTP_TARGET, "/api/transactions");
            
            // Add custom fintech attributes
            span.setAttribute("fintech.transaction.id", transaction.getTransactionId());
            span.setAttribute("fintech.transaction.type", transaction.getType().toString());
            span.setAttribute("fintech.transaction.amount", transaction.getAmount().doubleValue());
            span.setAttribute("fintech.transaction.currency", transaction.getCurrency());
            span.setAttribute("fintech.sender.country", transaction.getSenderCountry());
            span.setAttribute("fintech.receiver.country", transaction.getReceiverCountry());
            span.setAttribute("fintech.payment.method", transaction.getPaymentMethod());
            
            // Process transaction
            Transaction processedTransaction = transactionService.processTransaction(transaction);
            
            // Add result attributes
            span.setAttribute("fintech.transaction.status", processedTransaction.getStatus().toString());
            span.setAttribute("fintech.risk.level", processedTransaction.getRiskLevel().toString());
            span.setAttribute("fintech.risk.score", processedTransaction.getRiskScore());
            span.setAttribute("fintech.fraud.detected", processedTransaction.isFraudDetected());
            
            if (processedTransaction.isFraudDetected()) {
                span.setAttribute("fintech.fraud.probability", processedTransaction.getFraudProbability());
            }
            
            // Add event
            span.addEvent("transaction_processed", io.opentelemetry.api.common.Attributes.builder()
                    .put("fintech.transaction.id", processedTransaction.getTransactionId())
                    .put("fintech.transaction.status", processedTransaction.getStatus().toString())
                    .build());
            
            // Set response status
            HttpStatus httpStatus = processedTransaction.getStatus() == Transaction.TransactionStatus.COMPLETED
                    ? HttpStatus.CREATED
                    : HttpStatus.ACCEPTED;
            
            span.setAttribute(SemanticAttributes.HTTP_STATUS_CODE, httpStatus.value());
            span.setStatus(StatusCode.OK);
            
            // Build response
            Map<String, Object> response = new HashMap<>();
            response.put("transactionId", processedTransaction.getTransactionId());
            response.put("status", processedTransaction.getStatus());
            response.put("riskLevel", processedTransaction.getRiskLevel());
            response.put("fraudDetected", processedTransaction.isFraudDetected());
            response.put("message", getStatusMessage(processedTransaction));
            
            return ResponseEntity.status(httpStatus).body(response);
            
        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR, "Transaction processing failed: " + e.getMessage());
            span.setAttribute(SemanticAttributes.HTTP_STATUS_CODE, 500);
            
            Map<String, Object> errorResponse = new HashMap<>();
            errorResponse.put("error", "Transaction processing failed");
            errorResponse.put("message", e.getMessage());
            
            return ResponseEntity.status(HttpStatus.INTERNAL_SERVER_ERROR).body(errorResponse);
            
        } finally {
            span.end();
        }
    }

    /**
     * Get transaction by ID
     * 
     * GET /api/transactions/{id}
     */
    @GetMapping("/{id}")
    public ResponseEntity<Transaction> getTransaction(@PathVariable String id) {
        Span span = tracer.spanBuilder("http.server.get_transaction")
                .setSpanKind(io.opentelemetry.api.trace.SpanKind.SERVER)
                .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            span.setAttribute(SemanticAttributes.HTTP_METHOD, "GET");
            span.setAttribute(SemanticAttributes.HTTP_ROUTE, "/api/transactions/{id}");
            span.setAttribute(SemanticAttributes.HTTP_TARGET, "/api/transactions/" + id);
            span.setAttribute("fintech.transaction.id", id);
            
            Transaction transaction = transactionService.getTransaction(id);
            
            if (transaction != null) {
                span.setAttribute(SemanticAttributes.HTTP_STATUS_CODE, 200);
                span.setStatus(StatusCode.OK);
                return ResponseEntity.ok(transaction);
            } else {
                span.setAttribute(SemanticAttributes.HTTP_STATUS_CODE, 404);
                span.setStatus(StatusCode.ERROR, "Transaction not found");
                return ResponseEntity.notFound().build();
            }
            
        } finally {
            span.end();
        }
    }

    /**
     * Health check endpoint
     */
    @GetMapping("/health")
    public ResponseEntity<Map<String, String>> health() {
        Map<String, String> response = new HashMap<>();
        response.put("status", "UP");
        response.put("service", "fintech-transaction-service");
        return ResponseEntity.ok(response);
    }

    /**
     * Get status message based on transaction state
     */
    private String getStatusMessage(Transaction transaction) {
        if (transaction.isFraudDetected()) {
            return "Transaction flagged for fraud review";
        } else if (transaction.getStatus() == Transaction.TransactionStatus.FLAGGED_FOR_REVIEW) {
            return "Transaction flagged for manual review";
        } else if (transaction.getStatus() == Transaction.TransactionStatus.COMPLETED) {
            return "Transaction completed successfully";
        } else if (transaction.getStatus() == Transaction.TransactionStatus.DECLINED) {
            return "Transaction declined due to risk assessment";
        } else {
            return "Transaction is being processed";
        }
    }
}

