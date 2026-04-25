# CICD 语义约定详解

> **标准来源**: OpenTelemetry Semantic Conventions v1.40.0 — CICD
> **稳定性状态**: 实验性 (Experimental)
> **核心目标**: 统一持续集成/持续部署（CI/CD）流水线事件的可观测性语义

---

## 一、背景

### 1.1 CI/CD 可观测性的价值

软件开发的核心流程——构建、测试、部署——长期以来是可观测性的盲区：

```text
传统可观测性:              CI/CD 可观测性:
服务运行时的指标/日志/追踪   构建成功率、测试耗时、部署频率

价值:
├── 识别构建流水线中的性能瓶颈（哪个阶段最慢？）
├── 量化部署对生产稳定性的影响（变更失败率）
├── 追踪制品（Artifact）从代码到生产的完整生命周期
├── 满足合规审计要求（谁、何时、部署了什么）
└── DORA 指标自动化采集（部署频率、变更前置时间、变更失败率、恢复时间）
```

### 1.2 为什么需要专门的语义约定？

CI/CD 事件具有独特的时间结构和实体关系：

- **流水线（Pipeline）**包含多个**阶段（Stage）**
- **阶段**包含多个**作业（Job）**
- **作业**在**运行器（Runner/Agent）**上执行
- 存在复杂的因果关系（一个构建触发多个部署）

没有标准化，各 CI 系统（GitHub Actions、GitLab CI、Jenkins、CircleCI）的遥测数据格式各异，无法统一分析。

---

## 二、核心概念与实体

### 2.1 CI/CD 实体层次

```text
CI/CD 实体层次:

Pipeline（流水线）
├── 触发原因: push, pull_request, scheduled, manual
├── 仓库: github.com/org/repo
├── 分支: main
│
├── Stage（阶段）: build
│   ├── Job（作业）: unit-tests
│   │   ├── Step（步骤）: setup-node
│   │   ├── Step（步骤）: npm-test
│   │   └── Step（步骤）: upload-results
│   └── Job（作业）: lint
│       └── ...
│
├── Stage（阶段）: deploy
│   └── Job（作业）: deploy-staging
│       └── Step（步骤）: kubectl-apply
│
└── Artifact（制品）: app-v1.2.3.jar
    └── 被下游 Pipeline 引用
```

### 2.2 实体映射到 OpenTelemetry

| CI/CD 实体 | OpenTelemetry 映射 | 说明 |
|-----------|-------------------|------|
| Pipeline | Trace / Root Span | 整个流水线作为一个 Trace |
| Stage | Span（INTERNAL） | Stage 作为 Span，父子关系表示串并行 |
| Job | Span（INTERNAL） | Job 作为 Stage 的子 Span |
| Step | Span（INTERNAL）或 Event | 细粒度步骤 |
| Runner/Agent | Resource | 执行环境的资源属性 |
| Artifact | Link | 跨 Trace 的制品关联 |

---

## 三、核心属性定义

### 3.1 流水线级属性

应用于 Pipeline Root Span 或 Resource：

| 属性键 | 类型 | 说明 | 必需性 |
|--------|------|------|--------|
| `cicd.pipeline.name` | string | 流水线名称 | 必须 |
| `cicd.pipeline.run.id` | string | 本次运行的唯一标识 | 必须 |
| `cicd.pipeline.run.url` | string | 本次运行的 Web URL | 推荐 |
| `cicd.pipeline.run.attempt` | int | 运行重试次数（从1开始）| 可选 |

### 3.2 触发与版本属性

| 属性键 | 类型 | 说明 | 必需性 |
|--------|------|------|--------|
| `cicd.trigger.source` | string | 触发源：`push`、`pull_request`、`schedule`、`webhook`、`manual` | 推荐 |
| `vcs.repository.url` | string | 版本控制仓库 URL | 推荐 |
| `vcs.ref.head` | string | Git 引用（分支或标签），如 `refs/heads/main` | 推荐 |
| `vcs.ref.head.type` | string | 引用类型：`branch`、`tag` | 可选 |
| `vcs.revision.commit` | string | 提交的完整 SHA | 推荐 |
| `vcs.revision.commit.short` | string | 提交的短 SHA（如 7 位）| 可选 |
| `vcs.change.title` | string | PR/MR 标题 | 可选 |
| `vcs.change.url` | string | PR/MR 的 Web URL | 可选 |

### 3.3 作业级属性

| 属性键 | 类型 | 说明 | 必需性 |
|--------|------|------|--------|
| `cicd.task.name` | string | 作业/任务名称 | 必须 |
| `cicd.task.type` | string | 任务类型：`build`、`test`、`deploy`、`publish`、`cleanup` | 推荐 |
| `cicd.task.run.url` | string | 本次作业运行的 Web URL | 可选 |

### 3.4 运行器/环境属性

| 属性键 | 类型 | 说明 | 必需性 |
|--------|------|------|--------|
| `cicd.system.name` | string | CI/CD 系统名称：`github_actions`、`gitlab_ci`、`jenkins`、`circleci`、`tekton` | 推荐 |
| `host.name` | string | 运行器主机名 | 可选 |
| `host.arch` | string | 运行器架构：`x86_64`、`arm64` | 可选 |
| `os.type` | string | 操作系统：`linux`、`windows`、`darwin` | 可选 |

### 3.5 制品属性

| 属性键 | 类型 | 说明 | 必需性 |
|--------|------|------|--------|
| `cicd.artifact.name` | string | 制品名称 | 必须 |
| `cicd.artifact.id` | string | 制品唯一标识 | 推荐 |
| `cicd.artifact.type` | string | 制品类型：`image`、`package`、`binary`、`report` | 可选 |

---

## 四、Span 建模

### 4.1 流水线 Trace 结构

```text
Trace: github-actions-deploy
├── Span: Pipeline — deploy-app (Root Span)
│   ├── 属性: cicd.pipeline.name=deploy-app
│   ├── 属性: cicd.pipeline.run.id=123456789
│   ├── 属性: cicd.trigger.source=push
│   ├── 属性: vcs.ref.head=refs/heads/main
│   ├── 属性: vcs.revision.commit=abc123def456...
│   │
│   ├── Span: Stage — build (INTERNAL)
│   │   ├── Span: Job — unit-tests (INTERNAL)
│   │   │   ├── Span: Step — checkout (INTERNAL)
│   │   │   ├── Span: Step — setup-node (INTERNAL)
│   │   │   ├── Span: Step — npm-test (INTERNAL)
│   │   │   │   └── 事件: test_result (pass/fail/skip)
│   │   │   └── Span: Step — upload-coverage (INTERNAL)
│   │   └── Span: Job — lint (INTERNAL)
│   │       └── ...
│   │
│   ├── Span: Stage — package (INTERNAL)
│   │   ├── Span: Job — build-docker-image (INTERNAL)
│   │   │   └── 事件: artifact_created
│   │   │       └── 属性: cicd.artifact.name=myapp:v1.2.3
│   │   └── Span: Job — push-to-registry (INTERNAL)
│   │
│   └── Span: Stage — deploy (INTERNAL)
│       ├── Span: Job — deploy-staging (INTERNAL)
│       └── Span: Job — deploy-production (INTERNAL)
│           └── Link → Trace: canary-analysis (关联到金丝雀分析流水线)
```

### 4.2 跨流水线关联

当制品从构建流水线传递到部署流水线时，使用 **Link** 建立跨 Trace 关联：

```java
// 在部署 Pipeline 的 Root Span 中链接到构建 Pipeline
Span deploySpan = tracer.spanBuilder("Pipeline — deploy")
    .addLink(
        buildPipelineSpanContext,  // 构建流水线的 SpanContext
        Attributes.builder()
            .put("cicd.artifact.name", "myapp:v1.2.3")
            .put("link.type", "artifact_producer")
            .build()
    )
    .startSpan();
```

---

## 五、多平台实现示例

### 5.1 GitHub Actions

GitHub Actions 可以通过 OpenTelemetry Action 自动发射遥测数据：

```yaml
# .github/workflows/ci.yml
name: CI

on: [push, pull_request]

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Setup OpenTelemetry
        uses: otel-ci-action/setup@v1
        with:
          otlp-endpoint: ${{ secrets.OTEL_ENDPOINT }}

      - name: Run Tests
        run: npm test
        # 此步骤自动创建 Span，携带 Step 级属性
```

手动实现时，可在工作流脚本中注入追踪：

```javascript
// GitHub Actions 自定义脚本中的追踪
const span = tracer.startSpan('Job — build');
span.setAttribute('cicd.task.name', 'build');
span.setAttribute('cicd.task.type', 'build');
span.setAttribute('cicd.system.name', 'github_actions');
span.setAttribute('vcs.ref.head', process.env.GITHUB_REF);
span.setAttribute('vcs.revision.commit', process.env.GITHUB_SHA);
span.setAttribute('vcs.repository.url', `${process.env.GITHUB_SERVER_URL}/${process.env.GITHUB_REPOSITORY}`);

// 执行构建步骤...

span.end();
```

### 5.2 GitLab CI

```yaml
# .gitlab-ci.yml
variables:
  OTEL_EXPORTER_OTLP_ENDPOINT: "https://otel-collector.company.com"

stages:
  - build
  - test
  - deploy

build-job:
  stage: build
  script:
    - otel-instrument -- npm run build
  variables:
    CICD_TASK_NAME: "build-job"
    CICD_TASK_TYPE: "build"
```

### 5.3 Jenkins

```groovy
// Jenkins Pipeline 中的 OpenTelemetry 集成
pipeline {
    agent any

    options {
        // 使用 OpenTelemetry Plugin 自动追踪整个 Pipeline
        openTelemetry()
    }

    stages {
        stage('Build') {
            steps {
                script {
                    currentSpan = otel.getCurrentSpan()
                    currentSpan.setAttribute('cicd.task.type', 'build')
                    currentSpan.setAttribute('vcs.ref.head', env.GIT_BRANCH)
                    currentSpan.setAttribute('vcs.revision.commit', env.GIT_COMMIT)
                }
                sh 'make build'
            }
        }
    }
}
```

---

## 六、DORA 指标采集

CI/CD 可观测性的核心价值之一是支撑 **DORA 四大指标**的自动化计算：

| DORA 指标 | 计算方式 | 依赖的 CI/CD 属性 |
|----------|---------|------------------|
| **部署频率** | 统计单位时间内的部署 Job 成功次数 | `cicd.task.type=deploy` + `status=OK` |
| **变更前置时间** | 从首次提交到部署成功的平均时间 | `vcs.revision.commit.time` → `deploy.end.time` |
| **变更失败率** | 导致生产故障的部署 / 总部署数 | 关联部署 Span 与生产故障事件 |
| **恢复时间** | 从故障发生到恢复的平均时间 | 关联告警事件与恢复部署事件 |

---

## 七、检查清单

- [ ] Pipeline Root Span 包含 `cicd.pipeline.name` 和 `cicd.pipeline.run.id`
- [ ] 版本信息完整：`vcs.repository.url`、`vcs.ref.head`、`vcs.revision.commit`
- [ ] 每个 Job/Stage 都有对应的 Span
- [ ] 制品创建事件记录了 `cicd.artifact.*` 属性
- [ ] 跨流水线通过 Link 关联制品来源
- [ ] 失败步骤正确记录 `status=ERROR` 和异常详情
- [ ] CI/CD 系统名称通过 `cicd.system.name` 标识

---

## 八、参考资源

- OpenTelemetry Semantic Conventions: CICD
- DORA Metrics: devops-research.com
- GitHub Actions: OpenTelemetry Integration
- GitLab CI: Pipeline Observability

---

> **总结**: CICD 语义约定将软件交付流水线从"黑盒执行"转化为"可观测的流程图"。通过标准化的 `cicd.*` 和 `vcs.*` 属性，团队可以精确度量构建效率、识别流水线瓶颈、追踪制品生命周期，并自动化采集 DORA 指标。
