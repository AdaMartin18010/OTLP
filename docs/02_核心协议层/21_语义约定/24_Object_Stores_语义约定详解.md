# Object Stores 语义约定详解

> **标准来源**: OpenTelemetry Semantic Conventions v1.40.0 — Object Stores
> **稳定性状态**: 实验性 (Experimental)
> **核心目标**: 统一对象存储操作（S3、GCS、Azure Blob 等）的可观测性语义

---

## 一、背景

### 1.1 对象存储的可观测性需求

对象存储（Object Storage）是现代应用的核心基础设施，用于存储非结构化数据：

```text
典型对象存储操作:
├── PUT    /bucket/object-key      → 上传对象
├── GET    /bucket/object-key      → 下载对象
├── DELETE /bucket/object-key      → 删除对象
├── LIST   /bucket/?prefix=...     → 列举对象
├── HEAD   /bucket/object-key      → 获取元数据
└── COPY   /bucket/src → /bucket/dst → 复制对象

可观测性需求:
├── 哪些服务在频繁读写对象存储？
├── 大文件上传/下载的性能瓶颈在哪？
├── 是否存在异常访问模式（如大量 LIST 操作）？
├── 存储成本归因（按服务、按操作类型）
└── 数据生命周期追踪（创建 → 访问 → 归档 → 删除）
```

### 1.2 为什么需要专门语义约定？

对象存储操作与数据库或消息系统有显著差异：

- **大对象**: 需要关注传输大小和分片（multipart）行为
- **最终一致性**: LIST 操作可能不立即反映最新写入
- **存储层级**: 标准存储、低频访问、归档、冷归档
- **预签名 URL**: 临时访问授权的追踪挑战

---

## 二、核心属性定义

### 2.1 操作级属性

| 属性键 | 类型 | 说明 | 必需性 |
|--------|------|------|--------|
| `object_store.bucket` | string | 存储桶名称 | 必须 |
| `object_store.key` | string | 对象键（路径）| 必须 |
| `object_store.operation` | string | 操作类型：`put`、`get`、`delete`、`list`、`head`、`copy` | 必须 |
| `object_store.destination.bucket` | string | 复制操作的目标桶 | 条件（copy 时必须）|
| `object_store.destination.key` | string | 复制操作的目标键 | 条件（copy 时必须）|

### 2.2 对象属性

| 属性键 | 类型 | 说明 | 必需性 |
|--------|------|------|--------|
| `object_store.object.size` | int | 对象大小（字节）| 推荐 |
| `object_store.object.class` | string | 存储类别：`STANDARD`、`INFREQUENT_ACCESS`、`ARCHIVE`、`COLD_ARCHIVE` | 可选 |
| `object_store.object.version_id` | string | 对象版本 ID（启用版本控制时）| 可选 |

### 2.3 分片上传属性

| 属性键 | 类型 | 说明 | 必需性 |
|--------|------|------|--------|
| `object_store.multipart.upload_id` | string | 分片上传任务 ID | 条件（multipart 时必须）|
| `object_store.multipart.part_number` | int | 当前分片序号 | 条件（分片上传时必须）|
| `object_store.multipart.parts_count` | int | 总分片数 | 可选 |

### 2.4 云厂商特定属性

| 属性键 | 类型 | 说明 | 适用厂商 |
|--------|------|------|---------|
| `cloud.provider` | string | `aws`、`gcp`、`azure` | 所有 |
| `cloud.region` | string | 区域代码，如 `us-east-1` | 所有 |
| `aws.s3.request_id` | string | AWS S3 请求 ID | AWS |
| `gcs.storage_generation` | string | GCS 对象生成号 | GCP |
| `azure.blob.lease_id` | string | Azure Blob 租约 ID | Azure |

---

## 三、Span 建模

### 3.1 基本操作

```text
PUT 操作示例:
Span: PUT s3://my-bucket/data/2026/04/report.csv (Span, CLIENT kind)
├── 属性: object_store.bucket=my-bucket
├── 属性: object_store.key=data/2026/04/report.csv
├── 属性: object_store.operation=put
├── 属性: object_store.object.size=5242880
├── 属性: object_store.object.class=STANDARD
├── 属性: cloud.provider=aws
├── 属性: cloud.region=us-east-1
├── 属性: http.request.method=PUT
└── 属性: url.full=https://s3.us-east-1.amazonaws.com/my-bucket/data/2026/04/report.csv
```

### 3.2 分片上传

```text
分片上传 Trace 结构:
Trace: multipart-upload-report
├── Span: InitiateMultipartUpload (CLIENT)
│   ├── 属性: object_store.operation=put
│   ├── 属性: object_store.multipart.upload_id=abc123...
│
├── Span: UploadPart 1 (CLIENT)
│   ├── 属性: object_store.operation=put
│   ├── 属性: object_store.multipart.upload_id=abc123...
│   └── 属性: object_store.multipart.part_number=1
│
├── Span: UploadPart 2 (CLIENT)
│   ├── 属性: object_store.operation=put
│   ├── 属性: object_store.multipart.upload_id=abc123...
│   └── 属性: object_store.multipart.part_number=2
│
└── Span: CompleteMultipartUpload (CLIENT)
    ├── 属性: object_store.operation=put
    └── 属性: object_store.multipart.upload_id=abc123...
```

### 3.3 LIST 操作

LIST 操作可能返回大量结果，需要关注分页：

```text
Span: LIST s3://my-bucket/?prefix=data/2026/ (CLIENT)
├── 属性: object_store.bucket=my-bucket
├── 属性: object_store.operation=list
├── 属性: object_store.key_prefix=data/2026/
├── 属性: object_store.list.max_keys=1000
└── 事件: pagination (如果结果分页)
    └── 属性: page_count=3
```

---

## 四、多语言实现示例

### 4.1 AWS S3 (JavaScript/Node.js)

```javascript
const { S3Client, PutObjectCommand } = require('@aws-sdk/client-s3');
const { trace } = require('@opentelemetry/api');

const tracer = trace.getTracer('s3-client');

async function uploadFile(bucket, key, body) {
  const span = tracer.startSpan(`PUT s3://${bucket}/${key}`, {
    kind: SpanKind.CLIENT,
    attributes: {
      'object_store.bucket': bucket,
      'object_store.key': key,
      'object_store.operation': 'put',
      'object_store.object.size': Buffer.byteLength(body),
      'cloud.provider': 'aws',
    }
  });

  try {
    const client = new S3Client({ region: 'us-east-1' });
    const command = new PutObjectCommand({
      Bucket: bucket,
      Key: key,
      Body: body,
    });

    const response = await client.send(command);
    span.setAttribute('aws.s3.request_id', response.RequestId);
    span.setStatus({ code: SpanStatusCode.OK });
  } catch (error) {
    span.recordException(error);
    span.setStatus({ code: SpanStatusCode.ERROR, message: error.message });
    throw error;
  } finally {
    span.end();
  }
}
```

### 4.2 GCS (Python)

```python
from google.cloud import storage
from opentelemetry import trace

tracer = trace.get_tracer(__name__)

def download_blob(bucket_name, source_blob_name, destination_file_name):
    with tracer.start_as_current_span(
        f"GET gs://{bucket_name}/{source_blob_name}",
        kind=trace.SpanKind.CLIENT,
        attributes={
            "object_store.bucket": bucket_name,
            "object_store.key": source_blob_name,
            "object_store.operation": "get",
            "cloud.provider": "gcp",
        }
    ) as span:
        client = storage.Client()
        bucket = client.bucket(bucket_name)
        blob = bucket.blob(source_blob_name)

        blob.download_to_filename(destination_file_name)

        span.set_attribute("object_store.object.size", blob.size)
        span.set_attribute("gcs.storage_generation", blob.generation)
```

### 4.3 Azure Blob (Java)

```java
BlobClient blobClient = new BlobClientBuilder()
    .endpoint("https://myaccount.blob.core.windows.net")
    .containerName("my-container")
    .blobName("data/report.csv")
    .buildClient();

Span span = tracer.spanBuilder("PUT azure://my-container/data/report.csv")
    .setSpanKind(SpanKind.CLIENT)
    .setAttribute("object_store.bucket", "my-container")
    .setAttribute("object_store.key", "data/report.csv")
    .setAttribute("object_store.operation", "put")
    .setAttribute("cloud.provider", "azure")
    .startSpan();

try {
    blobClient.upload(dataStream, dataLength, true);
    span.setStatus(StatusCode.OK);
} catch (Exception e) {
    span.recordException(e);
    span.setStatus(StatusCode.ERROR);
    throw e;
} finally {
    span.end();
}
```

---

## 五、成本优化与可观测性

对象存储成本与操作类型和存储层级密切相关。通过可观测性数据可以：

```text
成本分析查询:

1. 高频小对象 PUT 操作 → 可能适合改用批量上传或压缩
2. 大量 LIST 操作 → 可能表明对象组织不合理（前缀设计差）
3. 标准存储中的冷数据 → 触发生命周期策略迁移到低频/归档
4. 跨区域 GET → 可能需要在目标区域部署副本
```

---

## 六、检查清单

- [ ] 每个对象操作 Span 包含 `object_store.bucket` 和 `object_store.key`
- [ ] `object_store.operation` 正确标记为 put/get/delete/list/head/copy
- [ ] 上传/下载操作记录了 `object_store.object.size`
- [ ] 分片上传记录了 `object_store.multipart.upload_id` 和 `part_number`
- [ ] 云厂商属性（`cloud.provider`、`cloud.region`）已设置
- [ ] 复制操作同时记录了源和目标的 bucket/key
- [ ] 存储层级信息（如适用）通过 `object_store.object.class` 记录

---

## 七、参考资源

- OpenTelemetry Semantic Conventions: Object Stores
- AWS S3 API Reference
- Google Cloud Storage JSON API
- Azure Blob Storage REST API

---

> **总结**: Object Stores 语义约定将对象存储操作从"隐式的 HTTP 调用"提升为"显式的存储操作语义"。通过 `object_store.*` 属性，团队可以精确分析存储访问模式、识别成本优化机会，并追踪数据在对象存储中的完整生命周期。
