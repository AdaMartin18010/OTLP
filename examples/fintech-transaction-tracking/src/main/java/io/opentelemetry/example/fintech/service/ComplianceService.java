package io.opentelemetry.example.fintech.service;

import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.StatusCode;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Scope;
import io.opentelemetry.example.fintech.model.Transaction;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

/**
 * Compliance Service
 * 
 * Performs compliance checks for financial transactions:
 * - AML (Anti-Money Laundering)
 * - KYC (Know Your Customer)
 * - PCI-DSS validation
 * - Regulatory jurisdiction checks
 */
@Service
public class ComplianceService {

    @Autowired
    private Tracer tracer;

    /**
     * Perform comprehensive compliance check
     */
    public void performComplianceCheck(Transaction transaction) {
        Span span = tracer.spanBuilder("compliance.check")
                .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            // Add attributes
            span.setAttribute("fintech.transaction.id", transaction.getTransactionId());
            span.setAttribute("fintech.compliance.level", transaction.getComplianceLevel());
            
            // Sub-check 1: KYC verification
            performKycCheck(transaction);
            
            // Sub-check 2: AML check
            performAmlCheck(transaction);
            
            // Sub-check 3: Regulatory jurisdiction check
            checkRegulatoryJurisdiction(transaction);
            
            // Add result attributes
            span.setAttribute("fintech.compliance.kyc_verified", transaction.isKycVerified());
            span.setAttribute("fintech.compliance.aml_checked", transaction.isAmlChecked());
            span.setAttribute("fintech.compliance.jurisdiction", transaction.getRegulatoryJurisdiction());
            
            // Add event
            span.addEvent("compliance_check_completed", io.opentelemetry.api.common.Attributes.builder()
                    .put("fintech.compliance.kyc_verified", transaction.isKycVerified())
                    .put("fintech.compliance.aml_checked", transaction.isAmlChecked())
                    .build());
            
            span.setStatus(StatusCode.OK);
            
        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR, "Compliance check failed");
            throw new RuntimeException("Compliance check failed", e);
            
        } finally {
            span.end();
        }
    }

    /**
     * Perform KYC verification check
     */
    private void performKycCheck(Transaction transaction) {
        Span span = tracer.spanBuilder("compliance.kyc_check")
                .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            span.setAttribute("fintech.transaction.id", transaction.getTransactionId());
            span.setAttribute("fintech.sender.id", transaction.getSenderId());
            span.setAttribute("fintech.receiver.id", transaction.getReceiverId());
            
            // Simulate KYC verification (in production, call external KYC service)
            boolean kycVerified = performKycVerification(transaction);
            transaction.setKycVerified(kycVerified);
            
            span.setAttribute("fintech.compliance.kyc_verified", kycVerified);
            span.setStatus(StatusCode.OK);
            
        } finally {
            span.end();
        }
    }

    /**
     * Perform AML check
     */
    private void performAmlCheck(Transaction transaction) {
        Span span = tracer.spanBuilder("compliance.aml_check")
                .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            span.setAttribute("fintech.transaction.id", transaction.getTransactionId());
            span.setAttribute("fintech.transaction.amount", transaction.getAmount().doubleValue());
            span.setAttribute("fintech.transaction.is_cross_border", transaction.isCrossBorder());
            
            // Simulate AML check (in production, call external AML service)
            boolean amlPassed = performAmlVerification(transaction);
            transaction.setAmlChecked(amlPassed);
            
            span.setAttribute("fintech.compliance.aml_checked", amlPassed);
            
            if (!amlPassed) {
                span.addEvent("aml_flag_raised", io.opentelemetry.api.common.Attributes.builder()
                        .put("fintech.transaction.id", transaction.getTransactionId())
                        .build());
            }
            
            span.setStatus(StatusCode.OK);
            
        } finally {
            span.end();
        }
    }

    /**
     * Check regulatory jurisdiction
     */
    private void checkRegulatoryJurisdiction(Transaction transaction) {
        Span span = tracer.spanBuilder("compliance.jurisdiction_check")
                .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            span.setAttribute("fintech.sender.country", transaction.getSenderCountry());
            span.setAttribute("fintech.receiver.country", transaction.getReceiverCountry());
            
            // Determine regulatory jurisdiction
            String jurisdiction = determineJurisdiction(transaction);
            transaction.setRegulatoryJurisdiction(jurisdiction);
            
            span.setAttribute("fintech.compliance.jurisdiction", jurisdiction);
            span.setStatus(StatusCode.OK);
            
        } finally {
            span.end();
        }
    }

    /**
     * Simulate KYC verification (in production, call external service)
     */
    private boolean performKycVerification(Transaction transaction) {
        // For demo: randomly verify 80% of transactions
        // In production, check against KYC database
        return Math.random() > 0.2;
    }

    /**
     * Simulate AML verification (in production, call external service)
     */
    private boolean performAmlVerification(Transaction transaction) {
        // For demo: fail AML for high-value cross-border transactions 10% of the time
        if (transaction.isHighValue() && transaction.isCrossBorder()) {
            return Math.random() > 0.1;
        }
        return true;
    }

    /**
     * Determine regulatory jurisdiction
     */
    private String determineJurisdiction(Transaction transaction) {
        String senderCountry = transaction.getSenderCountry();
        String receiverCountry = transaction.getReceiverCountry();
        
        if (senderCountry.equals("US") || receiverCountry.equals("US")) {
            return "US-SEC";
        } else if (senderCountry.startsWith("EU-") || receiverCountry.startsWith("EU-")) {
            return "EU-MiFID";
        } else if (senderCountry.equals("UK") || receiverCountry.equals("UK")) {
            return "UK-FCA";
        } else {
            return "INTL-FATF";
        }
    }
}

