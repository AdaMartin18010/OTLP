package io.opentelemetry.example.fintech;

import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;

/**
 * FinTech Transaction Tracking Application
 * 
 * Demonstrates OpenTelemetry instrumentation for financial transaction processing
 * with compliance attributes, risk scoring, and fraud detection.
 * 
 * Key Features:
 * - Custom vendor-prefixed attributes (fintech.*)
 * - Standard semantic conventions (HTTP, DB, Messaging)
 * - Compliance attributes (PCI-DSS, AML, KYC)
 * - Risk scoring and fraud detection attributes
 * - Multi-currency support
 * 
 * @author OTLP Project Team
 * @version 1.0.0
 * @since 2025-10-20
 */
@SpringBootApplication
public class FintechTransactionApplication {

    public static void main(String[] args) {
        SpringApplication.run(FintechTransactionApplication.class, args);
        
        System.out.println("💰 FinTech Transaction Tracking Application Started");
        System.out.println("📊 Sending transaction traces to OTLP Collector at http://localhost:4318");
        System.out.println("🔗 API Documentation: http://localhost:8080/swagger-ui.html");
        System.out.println("🔍 Health Check: http://localhost:8080/actuator/health");
        System.out.println();
        System.out.println("📖 Example API calls:");
        System.out.println("  POST http://localhost:8080/api/transactions");
        System.out.println("  GET  http://localhost:8080/api/transactions/{id}");
    }
}

