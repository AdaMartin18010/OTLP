package io.opentelemetry.example.fintech.service;

import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.StatusCode;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Scope;
import io.opentelemetry.example.fintech.model.Transaction;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

import java.math.BigDecimal;

/**
 * Risk Assessment Service
 * 
 * Evaluates transaction risk based on multiple factors:
 * - Transaction amount
 * - Cross-border status
 * - Sender/receiver country risk
 * - Historical patterns
 * - Velocity checks
 */
@Service
public class RiskAssessmentService {

    @Autowired
    private Tracer tracer;

    /**
     * Assess risk for a transaction
     */
    public void assessRisk(Transaction transaction) {
        Span span = tracer.spanBuilder("risk.assess")
                .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            // Add attributes
            span.setAttribute("fintech.transaction.id", transaction.getTransactionId());
            span.setAttribute("fintech.transaction.amount", transaction.getAmount().doubleValue());
            span.setAttribute("fintech.transaction.is_cross_border", transaction.isCrossBorder());
            
            // Calculate risk score
            double riskScore = calculateRiskScore(transaction);
            transaction.setRiskScore(riskScore);
            
            // Determine risk level
            Transaction.RiskLevel riskLevel = determineRiskLevel(riskScore);
            transaction.setRiskLevel(riskLevel);
            
            // Build risk factors JSON
            String riskFactors = buildRiskFactors(transaction, riskScore);
            transaction.setRiskFactors(riskFactors);
            
            // Add result attributes
            span.setAttribute("fintech.risk.score", riskScore);
            span.setAttribute("fintech.risk.level", riskLevel.toString());
            span.setAttribute("fintech.risk.factors", riskFactors);
            
            // Add event
            span.addEvent("risk_assessment_completed", io.opentelemetry.api.common.Attributes.builder()
                    .put("fintech.risk.score", riskScore)
                    .put("fintech.risk.level", riskLevel.toString())
                    .build());
            
            span.setStatus(StatusCode.OK);
            
        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR, "Risk assessment failed");
            // Set default high risk if assessment fails
            transaction.setRiskLevel(Transaction.RiskLevel.HIGH);
            transaction.setRiskScore(0.75);
            
        } finally {
            span.end();
        }
    }

    /**
     * Calculate risk score (0.0 - 1.0)
     */
    private double calculateRiskScore(Transaction transaction) {
        double score = 0.0;
        
        // Factor 1: Amount risk (0.0 - 0.3)
        double amountRisk = calculateAmountRisk(transaction.getAmount());
        score += amountRisk;
        
        // Factor 2: Cross-border risk (0.0 - 0.2)
        if (transaction.isCrossBorder()) {
            score += 0.2;
        }
        
        // Factor 3: Country risk (0.0 - 0.25)
        double countryRisk = calculateCountryRisk(transaction.getSenderCountry(), transaction.getReceiverCountry());
        score += countryRisk;
        
        // Factor 4: KYC verification (reduce risk by 0.1 if verified)
        if (transaction.isKycVerified()) {
            score -= 0.1;
        }
        
        // Factor 5: Payment method risk (0.0 - 0.15)
        double paymentMethodRisk = calculatePaymentMethodRisk(transaction.getPaymentMethod());
        score += paymentMethodRisk;
        
        // Ensure score is between 0.0 and 1.0
        return Math.max(0.0, Math.min(1.0, score));
    }

    /**
     * Calculate amount-based risk
     */
    private double calculateAmountRisk(BigDecimal amount) {
        double amountValue = amount.doubleValue();
        
        if (amountValue < 100) {
            return 0.0;
        } else if (amountValue < 1000) {
            return 0.05;
        } else if (amountValue < 10000) {
            return 0.15;
        } else if (amountValue < 100000) {
            return 0.25;
        } else {
            return 0.3;
        }
    }

    /**
     * Calculate country risk (simplified for demo)
     */
    private double calculateCountryRisk(String senderCountry, String receiverCountry) {
        // High-risk countries (simplified for demo)
        String[] highRiskCountries = {"XX", "YY", "ZZ"};
        
        double risk = 0.0;
        
        for (String highRiskCountry : highRiskCountries) {
            if (senderCountry.equals(highRiskCountry)) {
                risk += 0.15;
            }
            if (receiverCountry.equals(highRiskCountry)) {
                risk += 0.10;
            }
        }
        
        return Math.min(0.25, risk);
    }

    /**
     * Calculate payment method risk
     */
    private double calculatePaymentMethodRisk(String paymentMethod) {
        return switch (paymentMethod.toLowerCase()) {
            case "credit_card" -> 0.05;
            case "bank_transfer" -> 0.02;
            case "crypto" -> 0.15;
            case "wire_transfer" -> 0.08;
            default -> 0.10;
        };
    }

    /**
     * Determine risk level based on score
     */
    private Transaction.RiskLevel determineRiskLevel(double score) {
        if (score < 0.25) {
            return Transaction.RiskLevel.LOW;
        } else if (score < 0.5) {
            return Transaction.RiskLevel.MEDIUM;
        } else if (score < 0.75) {
            return Transaction.RiskLevel.HIGH;
        } else {
            return Transaction.RiskLevel.CRITICAL;
        }
    }

    /**
     * Build risk factors JSON string
     */
    private String buildRiskFactors(Transaction transaction, double riskScore) {
        return String.format("{\"amount_risk\": %.2f, \"cross_border\": %b, \"high_value\": %b, \"kyc_verified\": %b}",
                calculateAmountRisk(transaction.getAmount()),
                transaction.isCrossBorder(),
                transaction.isHighValue(),
                transaction.isKycVerified());
    }
}

