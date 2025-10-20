package io.opentelemetry.example.fintech.model;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.math.BigDecimal;
import java.time.Instant;

/**
 * Financial Transaction Model
 * 
 * Represents a financial transaction with comprehensive attributes
 * for compliance, risk assessment, and fraud detection.
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class Transaction {
    
    // Basic transaction information
    private String transactionId;
    private TransactionType type;
    private TransactionStatus status;
    private BigDecimal amount;
    private String currency;
    private Instant timestamp;
    
    // Parties involved
    private String senderId;
    private String senderAccountNumber;
    private String senderName;
    private String senderCountry;
    
    private String receiverId;
    private String receiverAccountNumber;
    private String receiverName;
    private String receiverCountry;
    
    // Compliance attributes
    private String complianceLevel; // e.g., "pci-dss-level-1", "aml-verified"
    private boolean kycVerified;
    private boolean amlChecked;
    private String regulatoryJurisdiction; // e.g., "US-SEC", "EU-MiFID"
    
    // Risk assessment
    private RiskLevel riskLevel;
    private Double riskScore; // 0.0 - 1.0
    private String riskFactors; // JSON string of risk factors
    
    // Fraud detection
    private boolean fraudDetected;
    private Double fraudProbability; // 0.0 - 1.0
    private String fraudIndicators; // JSON string of fraud indicators
    
    // Business context
    private String merchantId;
    private String merchantCategory; // MCC code
    private String paymentMethod; // credit_card, bank_transfer, crypto, etc.
    private String transactionCategory; // domestic, international, high-value
    
    // Additional metadata
    private String ipAddress;
    private String userAgent;
    private String deviceFingerprint;
    
    /**
     * Transaction Type Enum
     */
    public enum TransactionType {
        PAYMENT,
        TRANSFER,
        WITHDRAWAL,
        DEPOSIT,
        REFUND,
        CHARGEBACK
    }
    
    /**
     * Transaction Status Enum
     */
    public enum TransactionStatus {
        PENDING,
        PROCESSING,
        COMPLETED,
        FAILED,
        DECLINED,
        FLAGGED_FOR_REVIEW,
        REVERSED
    }
    
    /**
     * Risk Level Enum
     */
    public enum RiskLevel {
        LOW,
        MEDIUM,
        HIGH,
        CRITICAL
    }
    
    /**
     * Check if transaction is high-value (> $10,000)
     */
    public boolean isHighValue() {
        return amount.compareTo(new BigDecimal("10000")) > 0;
    }
    
    /**
     * Check if transaction is cross-border
     */
    public boolean isCrossBorder() {
        return !senderCountry.equals(receiverCountry);
    }
    
    /**
     * Check if transaction requires manual review
     */
    public boolean requiresManualReview() {
        return fraudDetected || 
               riskLevel == RiskLevel.HIGH || 
               riskLevel == RiskLevel.CRITICAL ||
               isHighValue();
    }
}

