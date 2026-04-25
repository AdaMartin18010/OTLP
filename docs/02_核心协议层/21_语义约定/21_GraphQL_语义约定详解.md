# GraphQL 语义约定详解

> **标准来源**: OpenTelemetry Semantic Conventions v1.40.0 — GraphQL
> **稳定性状态**: 实验性 (Experimental)
> **核心目标**: 统一 GraphQL 操作（查询、变更、订阅）的可观测性语义

---

## 一、背景

### 1.1 GraphQL 的可观测性挑战

GraphQL 与传统 REST API 的可观测性有本质差异：

```text
REST API:                GraphQL:
GET /users/123           POST /graphql
GET /orders?user=123     { body: "query { user(id: 123) { name orders { id } } }" }

挑战:
├── 单一端点: 所有请求都打到 /graphql，无法通过 URL 区分操作
├── 嵌套查询: 一个请求可能触发多个后端服务调用
├── 字段级选择性: 客户端决定返回哪些字段，相同操作名可能行为迥异
├── 解析器级追踪: 需要追踪每个字段解析器的性能
└── 批处理与 N+1: DataLoader 的批处理行为难以从外部观测
```

### 1.2 为什么需要专门的语义约定？

如果没有标准化，GraphQL 的可观测性会退化为：

- 所有 Span 都叫 `POST /graphql`
- 无法区分查询、变更、订阅
- 无法识别具体操作的语义（是 `GetUser` 还是 `CreateOrder`）
- 解析器性能黑盒化

---

## 二、核心属性定义

### 2.1 操作级属性

这些属性应用于代表整个 GraphQL 操作的 Span（通常是入口 Span）：

| 属性键 | 类型 | 说明 | 必需性 |
|--------|------|------|--------|
| `graphql.operation.name` | string | 操作名称（如有，来自 `query Name { ... }`）| 推荐 |
| `graphql.operation.type` | string | 操作类型：`query`、`mutation`、`subscription` | 必须 |
| `graphql.document` | string | 完整的 GraphQL 文档字符串（可截断）| 可选 |

### 2.2 解析器级属性

这些属性应用于代表字段解析器的 Span：

| 属性键 | 类型 | 说明 | 必需性 |
|--------|------|------|--------|
| `graphql.field.name` | string | 字段名称 | 必须 |
| `graphql.field.path` | string | 字段在查询树中的路径（如 `user.name`）| 推荐 |
| `graphql.field.return_type` | string | 字段的 GraphQL 返回类型（如 `String!`、`[Order]`）| 可选 |
| `graphql.field.parent_type` | string | 父对象的类型名称（如 `User`、`Query`）| 可选 |
| `graphql.data_loader.batch_size` | int | DataLoader 批处理的大小 | 可选 |

### 2.3 错误属性

| 属性键 | 类型 | 说明 | 必需性 |
|--------|------|------|--------|
| `graphql.error.count` | int | GraphQL 响应中的错误数量 | 推荐 |
| `graphql.error.path` | string | 错误对应的字段路径 | 可选 |

---

## 三、Span 建模

### 3.1 推荐的 Span 层次结构

```text
graphql.execute (Span, SERVER kind)
├── 属性: graphql.operation.type=query
├── 属性: graphql.operation.name=GetUserWithOrders
│
├── graphql.resolve (Span, INTERNAL kind)
│   ├── 属性: graphql.field.name=user
│   ├── 属性: graphql.field.path=user
│   └── 属性: graphql.field.return_type=User
│
├── graphql.resolve (Span, INTERNAL kind)
│   ├── 属性: graphql.field.name=name
│   ├── 属性: graphql.field.path=user.name
│   └── 属性: graphql.field.return_type=String!
│
├── graphql.resolve (Span, INTERNAL kind)
│   ├── 属性: graphql.field.name=orders
│   ├── 属性: graphql.field.path=user.orders
│   ├── 属性: graphql.field.return_type=[Order]
│   └── 属性: graphql.data_loader.batch_size=5
│       │
│       ├── db.query (Span, CLIENT kind)
│       │   └── SQL: SELECT * FROM orders WHERE user_id IN (...)
│       │
│       └── graphql.resolve (Span, INTERNAL kind)
│           ├── 属性: graphql.field.name=id
│           └── 属性: graphql.field.path=user.orders.id
```

### 3.2 Span 命名规范

| 层级 | Span 名称 | 示例 |
|------|----------|------|
| 操作层 | `graphql.execute <OperationName>` | `graphql.execute GetUserWithOrders` |
| 解析器层 | `graphql.resolve <Type>.<Field>` | `graphql.resolve User.name` |

如果操作没有名称，使用：

- `graphql.execute query`（匿名查询）
- `graphql.execute mutation`（匿名变更）

---

## 四、多语言实现示例

### 4.1 JavaScript/Node.js (apollo-server-plugin)

```javascript
// Apollo Server OpenTelemetry 插件示例
const { SemanticAttributes } = require('@opentelemetry/semantic-conventions');

const openTelemetryPlugin = {
  async requestDidStart() {
    return {
      async didResolveOperation(requestContext) {
        const span = trace.getActiveSpan();
        if (span) {
          span.setAttribute('graphql.operation.type', requestContext.operation?.operation);
          span.setAttribute('graphql.operation.name', requestContext.operationName || 'anonymous');
          span.setAttribute('graphql.document', requestContext.request.query?.substring(0, 1000));
        }
      },
      async didEncounterErrors(requestContext) {
        const span = trace.getActiveSpan();
        if (span) {
          span.setAttribute('graphql.error.count', requestContext.errors?.length || 0);
          requestContext.errors?.forEach((err, idx) => {
            span.recordException(err);
          });
        }
      }
    };
  }
};
```

### 4.2 Java (graphql-java)

```java
// graphql-java Instrumentation 实现
public class OpenTelemetryInstrumentation implements Instrumentation {
    private final Tracer tracer;

    @Override
    public InstrumentationContext<ExecutionResult> beginExecution(InstrumentationExecutionParameters params) {
        Span span = tracer.spanBuilder("graphql.execute " + (params.getOperation() != null ? params.getOperation() : "anonymous"))
            .setSpanKind(SpanKind.SERVER)
            .setAttribute("graphql.operation.type", params.getQuery().substring(0, Math.min(params.getQuery().length(), 1000)))
            .startSpan();

        return new SimpleInstrumentationContext<>() {
            @Override
            public void onCompleted(ExecutionResult result, Throwable t) {
                if (result.getErrors() != null && !result.getErrors().isEmpty()) {
                    span.setAttribute("graphql.error.count", result.getErrors().size());
                }
                if (t != null) {
                    span.recordException(t);
                    span.setStatus(StatusCode.ERROR);
                }
                span.end();
            }
        };
    }

    @Override
    public InstrumentationContext<Object> beginFieldFetch(InstrumentationFieldFetchParameters params) {
        ExecutionStepInfo stepInfo = params.getExecutionStepInfo();
        String path = stepInfo.getPath().toString();

        Span span = tracer.spanBuilder("graphql.resolve " + stepInfo.getParentTypeInfo().getTypeName() + "." + stepInfo.getFieldDefinition().getName())
            .setSpanKind(SpanKind.INTERNAL)
            .setAttribute("graphql.field.name", stepInfo.getFieldDefinition().getName())
            .setAttribute("graphql.field.path", path)
            .setAttribute("graphql.field.return_type", stepInfo.getFieldDefinition().getType().toString())
            .startSpan();

        return new SimpleInstrumentationContext<>() {
            @Override
            public void onCompleted(Object result, Throwable t) {
                if (t != null) {
                    span.recordException(t);
                    span.setStatus(StatusCode.ERROR);
                }
                span.end();
            }
        };
    }
}
```

### 4.3 Python (strawberry-graphql / graphene)

```python
from opentelemetry import trace
from opentelemetry.trace import SpanKind

tracer = trace.get_tracer(__name__)

class TelemetryMiddleware:
    """Strawberry / GraphQL 中间件示例"""

    async def resolve(self, next, root, info, **args):
        field_name = info.field_name
        parent_type = info.parent_type.name
        path = ".".join([str(p) for p in info.path.as_list()])

        with tracer.start_as_current_span(
            f"graphql.resolve {parent_type}.{field_name}",
            kind=SpanKind.INTERNAL,
        ) as span:
            span.set_attribute("graphql.field.name", field_name)
            span.set_attribute("graphql.field.path", path)
            span.set_attribute("graphql.field.parent_type", parent_type)

            try:
                result = await next(root, info, **args)
                return result
            except Exception as e:
                span.record_exception(e)
                span.set_status(trace.StatusCode.ERROR, str(e))
                raise
```

---

## 五、特殊场景处理

### 5.1 订阅（Subscription）

订阅操作的生命周期不同于查询/变更：

```text
graphql.execute Subscription.OnNewMessage (Span, 长生命周期)
├── 属性: graphql.operation.type=subscription
│
├── graphql.resolve (Span)
│   └── 初始解析器执行
│
└── 每次事件推送:
    └── 可创建新的子 Span 或 Event 记录推送
```

建议：将订阅的初始建立作为一个 Span，每次事件推送作为 Event 或独立的子 Span。

### 5.2 DataLoader 批处理

DataLoader 是 GraphQL 性能优化的核心，但其批处理行为需要显式观测：

```java
// 在 DataLoader 的 batch function 中增加观测
DataLoader<String, User> userLoader = DataLoader.newMappedDataLoader(keys -> {
    Span span = tracer.spanBuilder("dataloader.batch.users")
        .setAttribute("graphql.data_loader.batch_size", keys.size())
        .startSpan();

    try {
        return CompletableFuture.supplyAsync(() -> {
            // 批量查询
            return userService.findByIds(keys);
        });
    } finally {
        span.end();
    }
});
```

### 5.3 查询解析错误

当 GraphQL 查询语法错误或验证失败时，**应该**在操作层 Span 中记录错误：

```text
graphql.execute anonymous (Span)
├── 属性: graphql.operation.type=query
├── 状态: ERROR
├── 属性: graphql.error.count=3
└── 事件: 记录每个 validation error
```

---

## 六、与 HTTP 语义约定的关系

GraphQL 通常通过 HTTP 传输，因此 GraphQL Span 与 HTTP Span 存在层次关系：

```text
HTTP POST /graphql (Span, SERVER kind)
├── 属性: http.request.method=POST
├── 属性: url.path=/graphql
│
└── graphql.execute GetUser (Span, INTERNAL kind)
    ├── 属性: graphql.operation.type=query
    └── ...
```

**注意**: 如果 HTTP 层和 GraphQL 执行层在同一个进程内，可以合并为一个 Span（HTTP Span 同时携带 GraphQL 属性），也可以保持两个层级。官方推荐在服务端框架中至少保留 GraphQL 执行层 Span。

---

## 七、检查清单

- [ ] 每个 GraphQL 操作都有 `graphql.operation.type` 属性
- [ ] 命名操作记录了 `graphql.operation.name`
- [ ] 每个字段解析器都有独立的 Span 或合理的采样策略（高频字段可能过于密集）
- [ ] 解析器 Span 包含 `graphql.field.name` 和 `graphql.field.path`
- [ ] 错误响应记录了 `graphql.error.count`
- [ ] DataLoader 批处理记录了 `graphql.data_loader.batch_size`
- [ ] 订阅操作的生命周期被正确处理（避免无限长 Span）

---

## 八、参考资源

- OpenTelemetry Semantic Conventions: GraphQL
- OpenTelemetry Semantic Conventions: HTTP
- graphql.org: Instrumentation Best Practices

---

> **总结**: GraphQL 的单一端点和嵌套解析器模型对传统可观测性提出了独特挑战。通过 `graphql.operation.*` 和 `graphql.field.*` 标准化属性，以及解析器级的 Span 建模，可以将 GraphQL 的"黑盒查询"转化为完全可观测的调用图，精确识别 N+1 问题、慢解析器和查询热点。
