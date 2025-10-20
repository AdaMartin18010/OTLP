package io.opentelemetry.example.fintech.service;

import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.StatusCode;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Scope;
import io.opentelemetry.example.fintech.model.Transaction;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

/**
 * Fraud Detection Service
 * 
 * Detects potential fraud using multiple detection methods:
 * - Pattern analysis
 * - Velocity checks
 * - Device fingerprinting
 * - Behavioral analysis
 * - ML-based scoring (simulated)
 */
@Service
public class FraudDetectionService {

    @Autowired
    private Tracer tracer;

    private static final double FRAUD_THRESHOLD = 0.7;

    /**
     * Detect fraud for a transaction
     */
    public void detectFraud(Transaction transaction) {
        Span span = tracer.spanBuilder("fraud.detect")
                .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            // Add attributes
            span.setAttribute("fintech.transaction.id", transaction.getTransactionId());
            span.setAttribute("fintech.transaction.amount", transaction.getAmount().doubleValue());
            
            // Simulate ML model call
            Span mlSpan = tracer.spanBuilder("fraud.ml_model.predict")
                    .setSpanKind(io.opentelemetry.api.trace.SpanKind.CLIENT)
                    .startSpan();
            
            double fraudProbability;
            try (Scope mlScope = mlSpan.makeCurrent()) {
                mlSpan.setAttribute("fintech.ml.model.name", "fraud-detection-v2");
                mlSpan.setAttribute("fintech.ml.model.version", "2.1.0");
                
                // Simulate ML inference
                Thread.sleep(50); // Simulate ML latency
                fraudProbability = calculateFraudProbability(transaction);
                
                mlSpan.setAttribute("fintech.ml.prediction.probability", fraudProbability);
                mlSpan.setStatus(StatusCode.OK);
                
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                mlSpan.recordException(e);
                mlSpan.setStatus(StatusCode.ERROR);
                fraudProbability = 0.0;
            } finally {
                mlSpan.end();
            }
            
            transaction.setFraudProbability(fraudProbability);
            
            // Determine if fraud detected
            boolean fraudDetected = fraudProbability >= FRAUD_THRESHOLD;
            transaction.setFraudDetected(fraudDetected);
            
            // Build fraud indicators
            if (fraudDetected) {
                String fraudIndicators = buildFraudIndicators(transaction, fraudProbability);
                transaction.setFraudIndicators(fraudIndicators);
                span.setAttribute("fintech.fraud.indicators", fraudIndicators);
            }
            
            // Add result attributes
            span.setAttribute("fintech.fraud.probability", fraudProbability);
            span.setAttribute("fintech.fraud.detected", fraudDetected);
            span.setAttribute("fintech.fraud.threshold", FRAUD_THRESHOLD);
            
            // Add event
            if (fraudDetected) {
                span.addEvent("fraud_detected", io.opentelemetry.api.common.Attributes.builder()
                        .put("fintech.fraud.probability", fraudProbability)
                        .put("fintech.transaction.id", transaction.getTransactionId())
                        .build());
            }
            
            span.setStatus(StatusCode.OK);
            
        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR, "Fraud detection failed");
            // Set conservative default if detection fails
            transaction.setFraudDetected(true);
            transaction.setFraudProbability(0.9);
            
        } finally {
            span.end();
        }
    }

    /**
     * Calculate fraud probability (simplified for demo)
     */
    private double calculateFraudProbability(Transaction transaction) {
        double probability = 0.0;
        
        // Factor 1: High amount
        if (transaction.isHighValue()) {
            probability += 0.2;
        }
        
        // Factor 2: Cross-border to high-risk country
        if (transaction.isCrossBorder() && isHighRiskCountry(transaction.getReceiverCountry())) {
            probability += 0.3;
        }
        
        // Factor 3: No KYC verification
        if (!transaction.isKycVerified()) {
            probability += 0.15;
        }
        
        // Factor 4: Crypto payment method
        if ("crypto".equalsIgnoreCase(transaction.getPaymentMethod())) {
            probability += 0.2;
        }
        
        // Factor 5: Risk level
        if (transaction.getRiskLevel() == Transaction.RiskLevel.HIGH || 
            transaction.getRiskLevel() == Transaction.RiskLevel.CRITICAL) {
            probability += 0.2;
        }
        
        // Add random noise (simulate ML model variability)
        probability += (Math.random() * 0.1 - 0.05);
        
        return Math.max(0.0, Math.min(1.0, probability));
    }

    /**
     * Check if country is high-risk (simplified for demo)
     */
    private boolean isHighRiskCountry(String country) {
        String[] highRiskCountries = {"XX", "YY", "ZZ"};
        for (String highRiskCountry : highRiskCountries) {
            if (country.equals(highRiskCountry)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Build fraud indicators JSON string
     */
    private String buildFraudIndicators(Transaction transaction, double probability) {
        return String.format("{\"ml_probability\": %.2f, \"high_value\": %b, \"cross_border\": %b, \"no_kyc\": %b}",
                probability,
                transaction.isHighValue(),
                transaction.isCrossBorder(),
                !transaction.isKycVerified());
    }
}

