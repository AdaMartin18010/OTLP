from opentelemetry import trace, metrics
from opentelemetry.sdk.resources import Resource
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter as GrpcSpanExporter
from opentelemetry.exporter.otlp.proto.http.trace_exporter import OTLPSpanExporter as HttpSpanExporter
from opentelemetry.sdk.metrics import MeterProvider
from opentelemetry.sdk.metrics.export import PeriodicExportingMetricReader
from opentelemetry.exporter.otlp.proto.grpc.metric_exporter import OTLPMetricExporter as GrpcMetricExporter
from opentelemetry.exporter.otlp.proto.http.metric_exporter import OTLPMetricExporter as HttpMetricExporter
from opentelemetry.trace import SpanKind
import time
import os

endpoint = os.getenv("OTEL_EXPORTER_OTLP_ENDPOINT", "http://localhost:4317")
protocol = os.getenv("OTEL_EXPORTER_OTLP_PROTOCOL", "grpc").lower()  # grpc | http/protobuf
insecure = os.getenv("OTEL_EXPORTER_OTLP_INSECURE", "true").lower() == "true"
service_name = os.getenv("OTEL_SERVICE_NAME", "minimal-python")

resource = Resource.create({"service.name": service_name})

tp = TracerProvider(resource=resource)
if protocol.startswith("http"):
    span_exporter = HttpSpanExporter(endpoint=endpoint, insecure=insecure)
else:
    span_exporter = GrpcSpanExporter(endpoint=endpoint, insecure=insecure)
tp.add_span_processor(BatchSpanProcessor(span_exporter))
trace.set_tracer_provider(tp)

if protocol.startswith("http"):
    metric_exporter = HttpMetricExporter(endpoint=endpoint, insecure=insecure)
else:
    metric_exporter = GrpcMetricExporter(endpoint=endpoint, insecure=insecure)
reader = PeriodicExportingMetricReader(metric_exporter)
mp = MeterProvider(resource=resource, metric_readers=[reader])
metrics.set_meter_provider(mp)

tracer = trace.get_tracer(service_name)
meter = metrics.get_meter(service_name)
counter = meter.create_counter("demo_requests")

with tracer.start_as_current_span("demo-span", kind=SpanKind.SERVER) as span:
    span.set_attribute("demo.attr", "value")
    counter.add(1)
    time.sleep(0.1)

print(f"sent one span and one metric via OTLP to {endpoint} using {protocol}")

