# OpenTelemetry完整知识图谱

> **类型**: 全局思维导图
> **用途**: 了解OpenTelemetry全貌
> **阅读方式**: 从整体到局部，逐层深入

---

## 🗺️ 全景视图

```mermaid
mindmap
  root((OpenTelemetry<br/>可观测性框架))
    📚 概念层
      可观测性三支柱
        Traces 分布式追踪
        Metrics 指标
        Logs 日志
        Profiles 性能剖析 🆕
      核心概念
        Context 上下文
        Propagation 传播
        Attributes 属性
        Resources 资源

    🛠️ 实现层
      SDK实现
        自动插桩
        手动插桩
        零代码插桩
      语言支持
        Java
        Go
        Python
        JavaScript
        .NET
        Rust
        其他

    🏗️ 架构层
      Collector
        Receivers
        Processors
        Exporters
        Extensions
      部署模式
        Agent模式
        Gateway模式
        Sidecar模式

    📋 规范层
      OTLP协议
        Protobuf定义
        gRPC传输
        HTTP传输
      Semantic Conventions
        通用约定
        HTTP语义
        DB语义
        GenAI语义 🆕

    🚀 应用层
      部署运维
        Docker
        Kubernetes
        云平台
      最佳实践
        采样策略
        性能优化
        安全加固
      故障排查

    🤖 前沿层
      GenAI可观测性
      eBPF自动插桩
      Profiles信号
      AI Agent追踪
```

---

## 📚 概念层详细展开

```mermaid
mindmap
  root((可观测性<br/>三支柱))
    🔍 Traces<br/>分布式追踪
      Span
        Span ID
        Parent Span ID
        Trace ID
        Start/End Time
        Attributes
        Events
        Links
        Status
      Trace
        Span树
        因果关系
        时间线
      传播协议
        W3C Trace Context
        B3 Propagation
        Jaeger Propagation

    📊 Metrics<br/>指标
      类型
        Counter 计数器
        Gauge 仪表盘
        Histogram 直方图
        Summary 摘要
      时间序列
        标签维度
        聚合方式
        基数控制
      导出模式
        Pull Prometheus
        Push OTLP

    📝 Logs<br/>日志
      结构化日志
         severity
        timestamp
        body
        attributes
      与Trace关联
        trace_id
        span_id
      收集方式
        直接导出
        通过Collector

    🔬 Profiles<br/>性能剖析 🆕
      类型
        CPU Profile
        Memory Profile
        Goroutine Profile
        Mutex Profile
      pprof格式
      持续剖析
      与Trace关联
```

---

## 🛠️ 实现层详细展开

```mermaid
mindmap
  root((SDK<br/>实现方式))
    🤖 自动插桩
      Java Agent
        Bytecode注入
        JVM TI
      Python
        Monkey Patching
      Node.js
        Require Hook
      .NET
        CLR Profiling
      优势
        零代码修改
        快速启动
        全面覆盖
      局限
        粒度较粗
        性能开销
        定制性弱

    ✍️ 手动插桩
      API调用
        Tracer
        Meter
        Logger
      场景
        业务逻辑追踪
        自定义指标
        关键路径
      优势
        精确控制
        业务上下文
        灵活定制
      最佳实践
        不要过度插桩
        使用语义约定
        关注性能

    ⚡ 零代码插桩 🆕
      eBPF技术
        内核态执行
        事件驱动
        安全沙箱
      OBI项目
        支持语言
        自动检测
        混合模式
      适用场景
        遗留系统
        第三方组件
        无源码服务
```

---

## 🏗️ 架构层详细展开

```mermaid
mindmap
  root((OpenTelemetry<br/>Collector))
    📥 Receivers
      OTLP
        gRPC
        HTTP
      Prometheus
      Jaeger
      Zipkin
      Kafka
      其他协议

    ⚙️ Processors
      Batch
        批量处理
        压缩
      Memory Limiter
        内存保护
        背压
      Attributes
        属性添加
        属性删除
      Filter
        数据过滤
      Resource
        资源属性
      Sampling
        头采样
        尾采样

    📤 Exporters
      OTLP
        标准协议
      Prometheus Remote Write
      Jaeger
      Kafka
      云服务商
        AWS
        Azure
        GCP

    🔌 Extensions
      Health Check
      pprof
      zpages
      Bearer Token Auth
```

---

## 📋 规范层详细展开

```mermaid
mindmap
  root((Semantic<br/>Conventions))
    🌐 通用
      资源属性
        service.name
        service.version
        deployment.environment
        host.name
      异常属性
        exception.type
        exception.message
        exception.stacktrace

    🌐 HTTP
      请求
        http.request.method
        http.request.body.size
      响应
        http.response.status_code
        http.response.body.size
      路由
        http.route
        url.path
        url.scheme

    💾 数据库
      连接
        database.system
        database.connection_string
      操作
        database.operation
        database.query.text
        database.query.parameter

    🤖 GenAI 🆕
      系统
        gen_ai.system
        gen_ai.request.model
      使用
        gen_ai.usage.input_tokens
        gen_ai.usage.output_tokens
      成本
        gen_ai.estimated_cost_usd
```

---

## 🚀 学习路径导图

```mermaid
mindmap
  root((学习路径))
    🔰 初学者路径
      第1步: 快速开始
        5分钟入门
        运行示例
        查看Trace
      第2步: 基础概念
        什么是可观测性
        三支柱介绍
        OpenTelemetry架构
      第3步: 实践
        自动插桩
        查看仪表板
        简单故障排查

    👨‍💻 开发者路径
      SDK深入
        手动插桩
        Context传播
        自定义属性
      Collector配置
        基础配置
        处理器使用
        多后端导出
      生产准备
        采样配置
        性能调优
        安全加固

    🏗️ 架构师路径
      大规模部署
        高可用Collector
        多租户方案
        边缘部署
      成本优化
        采样策略设计
        数据分级
        存储优化
      生态集成
        多后端方案
        云原生集成
        遗留系统集成

    🔬 研究者路径
      形式化验证
        协议验证
        正确性证明
      前沿技术
        GenAI观测
        eBPF技术
        Profiles信号
```

---

## 🎯 使用指南

### 如何使用本导图

1. **全景视图**: 了解OpenTelemetry全貌
2. **逐层深入**: 根据兴趣深入特定领域
3. **学习路径**: 选择适合自己的学习路线
4. **查漏补缺**: 检查知识盲区

### 导图配色说明

- 🟦 蓝色系: 概念/理论
- 🟩 绿色系: 实现/代码
- 🟨 黄色系: 架构/组件
- 🟪 紫色系: 规范/标准
- 🟥 红色系: 前沿/新兴

---

**导图版本**: v1.0
**更新日期**: 2026年3月15日
**维护者**: OTLP项目团队
