---
title: Java SDK高级特性
description: OpenTelemetry Java SDK高级功能详解
category: 核心实现
tags:
  - java
  - sdk
version: Java SDK 1.47.0
date: 2026-03-17
status: published
---

# Java SDK高级特性

> **SDK版本**: 1.47.0  
> **最后更新**: 2026-03-17  

---

## 1. 自动配置

```xml
<dependency>
    <groupId>io.opentelemetry</groupId>
    <artifactId>opentelemetry-sdk-extension-autoconfigure</artifactId>
    <version>1.47.0</version>
</dependency>
```

## 2. 上下文传播

```java
// 跨线程传播
CompletableFuture.runAsync(() -> {
    try (Scope scope = parentContext.makeCurrent()) {
        // 自动继承父span
    }
});
```

---

**最后更新**: 2026-03-17  
**状态**: Published
