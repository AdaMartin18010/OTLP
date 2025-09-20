module crosstrace-demo

go 1.21

require (
    go.opentelemetry.io/otel v1.27.0
    go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc v1.27.0
    go.opentelemetry.io/otel/sdk v1.27.0
    go.opentelemetry.io/otel/trace v1.27.0
    github.com/cilium/ebpf v0.12.3
    github.com/vishvananda/netlink v1.2.1-beta.2
)
