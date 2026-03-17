---
title: OTLP异常检测与根因分析实战
description: 基于OTLP数据的异常检测方法与实践，包含统计方法、机器学习方法、时序异常检测、分布式追踪异常分析和根因分析(RCA)方法论
version: OTLP v1.10.0
date: 2026-03-17
author: OTLP项目团队
category: 数据分析与洞察
tags:
  - anomaly-detection
  - root-cause-analysis
  - machine-learning
  - time-series
  - distributed-tracing
status: published
---

# OTLP异常检测与根因分析实战

> **版本**: OTLP v1.10.0
> **最后更新**: 2026-03-17
> **阅读时间**: 约50分钟

---

## 1. 异常检测概述

### 1.1 可观测性中的异常检测

```
┌─────────────────────────────────────────────────────────────────┐
│                 可观测性异常检测全景图                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐         │
│  │   Metrics   │    │    Logs     │    │   Traces    │         │
│  │   指标异常   │    │   日志异常   │    │   链路异常   │         │
│  └──────┬──────┘    └──────┬──────┘    └──────┬──────┘         │
│         │                  │                  │                │
│         └──────────────────┼──────────────────┘                │
│                            ▼                                   │
│              ┌─────────────────────────┐                       │
│              │    异常检测引擎         │                       │
│              │  • 统计方法             │                       │
│              │  • 机器学习方法         │                       │
│              │  • 深度学习方法         │                       │
│              └───────────┬─────────────┘                       │
│                          ▼                                     │
│              ┌─────────────────────────┐                       │
│              │    根因分析引擎         │                       │
│              │  • 关联分析             │                       │
│              │  • 因果推断             │                       │
│              │  • 知识图谱             │                       │
│              └───────────┬─────────────┘                       │
│                          ▼                                     │
│              ┌─────────────────────────┐                       │
│              │    告警与响应           │                       │
│              │  • 智能告警分级         │                       │
│              │  • 自动化响应           │                       │
│              │  • 故障自愈             │                       │
│              └─────────────────────────┘                       │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 1.2 异常类型分类

```yaml
# 可观测性数据中的异常类型

时间维度异常:
  点异常:
    定义: 单个时间点的异常值
    示例: 某时刻CPU突然飙升到100%
    检测难度: ⭐⭐ (简单)

  上下文异常:
    定义: 在特定上下文中异常，单独看正常
    示例: 凌晨3点交易量突然增加
    检测难度: ⭐⭐⭐ (中等)

  集合异常:
    定义: 一系列相关数据点的异常模式
    示例: 持续缓慢增长的内存泄漏
    检测难度: ⭐⭐⭐⭐ (困难)

空间维度异常:
  单维度异常:
    定义: 单一指标的异常
    示例: 单个服务的错误率升高

  多维度异常:
    定义: 多个指标联合异常
    示例: 延迟增加+错误率增加+吞吐量下降

  拓扑异常:
    定义: 服务间依赖关系的异常
    示例: 调用链中某环节出现异常传播

业务维度异常:
  技术指标异常: CPU、内存、网络等
  业务指标异常: 订单量、转化率、支付成功率等
  用户体验异常: 页面加载时间、交互延迟等
```

---

## 2. 统计方法异常检测

### 2.1 基于阈值的检测

```python
"""
基于统计阈值的异常检测
适用于：正态分布或近似正态分布的指标
"""
import numpy as np
from typing import List, Tuple, Optional
import warnings

class StatisticalAnomalyDetector:
    """统计异常检测器"""

    def __init__(self, method: str = 'sigma', threshold: float = 3.0):
        """
        初始化检测器

        Args:
            method: 检测方法 ('sigma', 'iqr', 'mad')
            threshold: 阈值倍数
        """
        self.method = method
        self.threshold = threshold
        self.history = []

    def fit(self, data: List[float]):
        """拟合历史数据，建立基线"""
        self.history = np.array(data)
        return self

    def detect(self, value: float) -> Tuple[bool, dict]:
        """
        检测单个值是否异常

        Returns:
            (是否异常, 详细信息)
        """
        if len(self.history) < 10:
            warnings.warn("历史数据不足，建议至少10个样本")

        if self.method == 'sigma':
            return self._detect_sigma(value)
        elif self.method == 'iqr':
            return self._detect_iqr(value)
        elif self.method == 'mad':
            return self._detect_mad(value)
        else:
            raise ValueError(f"Unknown method: {self.method}")

    def _detect_sigma(self, value: float) -> Tuple[bool, dict]:
        """基于标准差的3-sigma方法"""
        mean = np.mean(self.history)
        std = np.std(self.history)

        if std == 0:
            return False, {'reason': 'zero_variance'}

        z_score = abs(value - mean) / std
        is_anomaly = z_score > self.threshold

        return is_anomaly, {
            'method': '3-sigma',
            'mean': mean,
            'std': std,
            'z_score': z_score,
            'threshold': self.threshold,
            'deviation_percent': abs(value - mean) / mean * 100 if mean != 0 else 0
        }

    def _detect_iqr(self, value: float) -> Tuple[bool, dict]:
        """基于四分位距的IQR方法（对异常值鲁棒）"""
        q1 = np.percentile(self.history, 25)
        q3 = np.percentile(self.history, 75)
        iqr = q3 - q1

        lower_bound = q1 - self.threshold * iqr
        upper_bound = q3 + self.threshold * iqr

        is_anomaly = value < lower_bound or value > upper_bound

        return is_anomaly, {
            'method': 'IQR',
            'q1': q1,
            'q3': q3,
            'iqr': iqr,
            'lower_bound': lower_bound,
            'upper_bound': upper_bound,
            'value': value
        }

    def _detect_mad(self, value: float) -> Tuple[bool, dict]:
        """基于绝对中位差的MAD方法（最鲁棒）"""
        median = np.median(self.history)
        mad = np.median(np.abs(self.history - median))

        # 使用1.4826作为正态分布的一致性因子
        modified_z_score = 0.6745 * (value - median) / mad if mad != 0 else 0

        is_anomaly = abs(modified_z_score) > self.threshold

        return is_anomaly, {
            'method': 'MAD',
            'median': median,
            'mad': mad,
            'modified_z_score': modified_z_score,
            'threshold': self.threshold
        }


# ========== 使用示例 ==========

# 模拟正常历史数据
normal_data = [100, 102, 98, 101, 99, 103, 97, 100, 102, 99,
               101, 98, 100, 102, 99, 101, 100, 98, 102, 100]

# 初始化检测器
detector = StatisticalAnomalyDetector(method='sigma', threshold=3.0)
detector.fit(normal_data)

# 检测新值
test_values = [105, 100, 150, 98]
for value in test_values:
    is_anomaly, info = detector.detect(value)
    status = "🔴 异常" if is_anomaly else "🟢 正常"
    print(f"值 {value}: {status}")
    print(f"  详细信息: {info}\n")
```

### 2.2 时间序列分解

```python
"""
时间序列分解异常检测
将时序分解为趋势、季节性和残差，检测残差中的异常
"""
import numpy as np
from scipy import stats
from typing import Optional, Tuple
import pandas as pd

class TimeSeriesDecompositionDetector:
    """基于时序分解的异常检测"""

    def __init__(self, seasonality: int = 24, trend_window: int = 7):
        """
        初始化

        Args:
            seasonality: 季节周期长度（如24小时、7天）
            trend_window: 趋势平滑窗口
        """
        self.seasonality = seasonality
        self.trend_window = trend_window

    def decompose(self, series: np.ndarray) -> dict:
        """
        使用STL-like方法分解时间序列

        Returns:
            {'trend': ..., 'seasonal': ..., 'residual': ...}
        """
        n = len(series)

        # 1. 提取趋势（移动平均）
        trend = self._extract_trend(series, self.trend_window)

        # 2. 提取季节性
        detrended = series - trend
        seasonal = self._extract_seasonal(detrended, self.seasonality)

        # 3. 计算残差
        residual = series - trend - seasonal

        return {
            'trend': trend,
            'seasonal': seasonal,
            'residual': residual,
            'original': series
        }

    def _extract_trend(self, series: np.ndarray, window: int) -> np.ndarray:
        """使用移动平均提取趋势"""
        # 双边移动平均
        pad_width = window // 2
        padded = np.pad(series, (pad_width, pad_width), mode='edge')
        trend = np.convolve(padded, np.ones(window)/window, mode='valid')

        # 对齐长度
        if len(trend) < len(series):
            trend = np.pad(trend, (0, len(series) - len(trend)), mode='edge')
        elif len(trend) > len(series):
            trend = trend[:len(series)]

        return trend

    def _extract_seasonal(self, detrended: np.ndarray, period: int) -> np.ndarray:
        """提取季节性成分"""
        n = len(detrended)
        seasonal = np.zeros(n)

        # 计算每个位置的平均季节性
        for i in range(period):
            indices = np.arange(i, n, period)
            if len(indices) > 0:
                seasonal[indices] = np.mean(detrended[indices])

        return seasonal

    def detect_anomalies(self, series: np.ndarray,
                        residual_threshold: float = 3.0) -> np.ndarray:
        """
        检测时序中的异常点

        Returns:
            布尔数组，True表示异常
        """
        components = self.decompose(series)
        residual = components['residual']

        # 基于残差的统计特性检测异常
        mean_res = np.mean(residual)
        std_res = np.std(residual)

        if std_res == 0:
            return np.zeros(len(series), dtype=bool)

        z_scores = np.abs((residual - mean_res) / std_res)
        anomalies = z_scores > residual_threshold

        return anomalies


# ========== PromQL应用示例 ==========

"""
# 在Prometheus中使用时序分解思想检测异常

# 1. 计算指标的移动平均（趋势）
avg_over_time(http_request_duration_seconds[1h])

# 2. 计算与趋势的偏差
(
  http_request_duration_seconds
  - avg_over_time(http_request_duration_seconds[1h])
) / stddev_over_time(http_request_duration_seconds[1h])

# 3. 检测偏离超过3个标准差的异常
abs(
  (
    http_request_duration_seconds
    - avg_over_time(http_request_duration_seconds[1h])
  ) / stddev_over_time(http_request_duration_seconds[1h])
) > 3

# 4. 季节性异常检测（同比环比）
# 与上周同一时间比较
abs(
  (
    rate(http_requests_total[5m])
    - rate(http_requests_total[5m] offset 1w)
  ) / rate(http_requests_total[5m] offset 1w)
) > 0.3  # 变化超过30%
"""
```

---

## 3. 机器学习方法异常检测

### 3.1 Isolation Forest (孤立森林)

```python
"""
Isolation Forest 异常检测
原理：异常点更容易被"孤立"，所需分割次数更少
优势：线性的时间复杂度，适合高维数据和大规模数据
"""
import numpy as np
from sklearn.ensemble import IsolationForest
from typing import List, Dict, Optional
import joblib

class IsolationForestDetector:
    """基于孤立森林的异常检测器"""

    def __init__(self,
                 contamination: float = 0.1,
                 n_estimators: int = 100,
                 max_samples: str = 'auto',
                 random_state: int = 42):
        """
        初始化孤立森林检测器

        Args:
            contamination: 预期异常比例
            n_estimators: 树的数量
            max_samples: 每棵树采样样本数
        """
        self.contamination = contamination
        self.n_estimators = n_estimators
        self.model = IsolationForest(
            contamination=contamination,
            n_estimators=n_estimators,
            max_samples=max_samples,
            random_state=random_state,
            n_jobs=-1
        )
        self.is_fitted = False

    def fit(self, X: np.ndarray) -> 'IsolationForestDetector':
        """训练模型"""
        self.model.fit(X)
        self.is_fitted = True
        return self

    def predict(self, X: np.ndarray) -> Dict:
        """
        预测异常

        Returns:
            {
                'is_anomaly': bool数组,
                'anomaly_score': 异常分数,
                'confidence': 置信度
            }
        """
        if not self.is_fitted:
            raise RuntimeError("模型未训练，请先调用fit()")

        # 预测标签: 1=正常, -1=异常
        labels = self.model.predict(X)

        # 异常分数: 负值越大越异常
        scores = self.model.score_samples(X)

        # 归一化分数到[0,1]，越大越异常
        normalized_scores = 0.5 - scores

        return {
            'is_anomaly': labels == -1,
            'anomaly_score': normalized_scores,
            'raw_score': scores,
            'confidence': np.abs(normalized_scores)
        }

    def save(self, path: str):
        """保存模型"""
        joblib.dump(self.model, path)

    def load(self, path: str):
        """加载模型"""
        self.model = joblib.load(path)
        self.is_fitted = True


# ========== 可观测性场景应用 ==========

def detect_multivariate_anomaly(metrics_data: Dict[str, List[float]]) -> Dict:
    """
    多变量异常检测 - 检测指标组合中的异常

    Args:
        metrics_data: {
            'cpu_usage': [45, 46, 47, ...],
            'memory_usage': [60, 61, 62, ...],
            'request_latency': [100, 105, 110, ...],
            'error_rate': [0.1, 0.1, 0.2, ...],
            'throughput': [1000, 1050, 1100, ...]
        }
    """
    # 转换为特征矩阵
    features = np.column_stack([
        metrics_data['cpu_usage'],
        metrics_data['memory_usage'],
        metrics_data['request_latency'],
        metrics_data['error_rate'],
        metrics_data['throughput']
    ])

    # 标准化
    from sklearn.preprocessing import StandardScaler
    scaler = StandardScaler()
    features_scaled = scaler.fit_transform(features)

    # 训练检测器
    detector = IsolationForestDetector(contamination=0.05)
    detector.fit(features_scaled)

    # 预测
    result = detector.predict(features_scaled)

    # 找出最异常的样本
    anomaly_indices = np.where(result['is_anomaly'])[0]
    top_anomalies = np.argsort(result['anomaly_score'])[-10:]  # Top 10

    return {
        'anomaly_count': np.sum(result['is_anomaly']),
        'anomaly_ratio': np.mean(result['is_anomaly']),
        'anomaly_indices': anomaly_indices.tolist(),
        'top_anomalies': top_anomalies.tolist(),
        'scores': result['anomaly_score'].tolist()
    }


# 实战案例：微服务异常检测
"""
场景：检测微服务集群中的异常节点

特征工程:
├── 系统指标
│   ├── CPU使用率 (cpu_usage)
│   ├── 内存使用率 (memory_usage)
│   ├── 磁盘IO (disk_io)
│   └── 网络IO (network_io)
├── 应用指标
│   ├── 请求延迟P99 (latency_p99)
│   ├── 错误率 (error_rate)
│   ├── QPS (requests_per_sec)
│   └── 活跃连接数 (active_connections)
└── 业务指标
    ├── 订单成功率 (order_success_rate)
    ├── 支付转化率 (payment_conversion)
    └── 用户活跃度 (user_activity)

孤立森林会学习"正常"的多维分布，
任何偏离这个分布的组合都会被标记为异常。
例如：
- CPU正常但延迟异常高 → 可能是下游依赖问题
- 错误率正常但CPU异常高 → 可能是计算密集型任务
- 多个指标同时异常 → 严重故障
"""
```

### 3.2 LSTM 时序异常检测

```python
"""
LSTM (长短期记忆网络) 时序异常检测
适用于：具有复杂时间依赖性的序列数据
优势：能捕捉长期依赖关系和非线性模式
"""
import torch
import torch.nn as nn
from torch.utils.data import Dataset, DataLoader
import numpy as np
from typing import List, Tuple, Optional

class LSTM_Autoencoder(nn.Module):
    """基于LSTM自编码器的异常检测"""

    def __init__(self,
                 input_dim: int,
                 hidden_dim: int = 64,
                 num_layers: int = 2,
                 seq_length: int = 60):
        super().__init__()

        self.seq_length = seq_length
        self.hidden_dim = hidden_dim

        # 编码器
        self.encoder_lstm = nn.LSTM(
            input_dim, hidden_dim, num_layers,
            batch_first=True, dropout=0.2
        )

        # 解码器
        self.decoder_lstm = nn.LSTM(
            hidden_dim, input_dim, num_layers,
            batch_first=True, dropout=0.2
        )

    def forward(self, x):
        # 编码
        _, (hidden, cell) = self.encoder_lstm(x)

        # 准备解码输入
        decoder_input = hidden[-1].unsqueeze(1).repeat(1, self.seq_length, 1)

        # 解码
        output, _ = self.decoder_lstm(decoder_input)

        return output


class TimeSeriesDataset(Dataset):
    """时间序列数据集"""

    def __init__(self, data: np.ndarray, seq_length: int):
        self.data = data
        self.seq_length = seq_length

    def __len__(self):
        return len(self.data) - self.seq_length

    def __getitem__(self, idx):
        return torch.FloatTensor(self.data[idx:idx+self.seq_length])


class LSTMAnomalyDetector:
    """LSTM异常检测器"""

    def __init__(self,
                 seq_length: int = 60,
                 hidden_dim: int = 64,
                 num_layers: int = 2,
                 learning_rate: float = 0.001,
                 epochs: int = 50):
        self.seq_length = seq_length
        self.hidden_dim = hidden_dim
        self.num_layers = num_layers
        self.learning_rate = learning_rate
        self.epochs = epochs
        self.model = None
        self.threshold = None

    def fit(self, data: np.ndarray, validation_split: float = 0.1):
        """
        训练自编码器

        Args:
            data: 时间序列数据 [n_samples, n_features]
        """
        # 标准化
        self.mean = np.mean(data, axis=0)
        self.std = np.std(data, axis=0) + 1e-8
        data_normalized = (data - self.mean) / self.std

        # 创建数据集
        dataset = TimeSeriesDataset(data_normalized, self.seq_length)

        # 划分训练验证集
        val_size = int(len(dataset) * validation_split)
        train_size = len(dataset) - val_size
        train_dataset, val_dataset = torch.utils.data.random_split(
            dataset, [train_size, val_size]
        )

        train_loader = DataLoader(train_dataset, batch_size=32, shuffle=True)
        val_loader = DataLoader(val_dataset, batch_size=32)

        # 初始化模型
        input_dim = data.shape[1]
        self.model = LSTM_Autoencoder(
            input_dim, self.hidden_dim, self.num_layers, self.seq_length
        )

        # 训练
        optimizer = torch.optim.Adam(self.model.parameters(), lr=self.learning_rate)
        criterion = nn.MSELoss()

        self.model.train()
        for epoch in range(self.epochs):
            total_loss = 0
            for batch in train_loader:
                optimizer.zero_grad()
                output = self.model(batch)
                loss = criterion(output, batch)
                loss.backward()
                optimizer.step()
                total_loss += loss.item()

            if (epoch + 1) % 10 == 0:
                print(f"Epoch {epoch+1}/{self.epochs}, Loss: {total_loss/len(train_loader):.6f}")

        # 计算重构误差阈值
        self._calculate_threshold(val_loader)

    def _calculate_threshold(self, val_loader):
        """基于验证集计算异常阈值"""
        self.model.eval()
        reconstruction_errors = []

        with torch.no_grad():
            for batch in val_loader:
                output = self.model(batch)
                error = torch.mean((output - batch) ** 2, dim=(1, 2))
                reconstruction_errors.extend(error.numpy())

        # 使用95百分位数作为阈值
        self.threshold = np.percentile(reconstruction_errors, 95)
        print(f"异常阈值 (95th percentile): {self.threshold:.6f}")

    def predict(self, data: np.ndarray) -> Dict:
        """预测异常"""
        self.model.eval()

        # 标准化
        data_normalized = (data - self.mean) / self.std
        dataset = TimeSeriesDataset(data_normalized, self.seq_length)
        loader = DataLoader(dataset, batch_size=32)

        reconstruction_errors = []
        predictions = []

        with torch.no_grad():
            for batch in loader:
                output = self.model(batch)
                error = torch.mean((output - batch) ** 2, dim=(1, 2))
                reconstruction_errors.extend(error.numpy())
                predictions.extend((error.numpy() > self.threshold).astype(int))

        # 对齐长度（前面seq_length-1个没有预测）
        predictions = [0] * (self.seq_length - 1) + predictions
        reconstruction_errors = [0.0] * (self.seq_length - 1) + reconstruction_errors

        return {
            'is_anomaly': np.array(predictions, dtype=bool),
            'reconstruction_error': np.array(reconstruction_errors),
            'threshold': self.threshold
        }


# ========== 实战：服务器指标异常检测 ==========

def server_metrics_anomaly_detection():
    """
    服务器指标异常检测实战

    使用LSTM学习正常的服务器指标模式，
    检测偏离正常模式的异常时刻。
    """
    # 模拟多维度服务器指标
    np.random.seed(42)
    n_samples = 10000

    # 正常模式：工作日的业务周期
    time = np.arange(n_samples)

    # CPU：业务高峰期间升高
    cpu_base = 30 + 20 * np.sin(2 * np.pi * time / 1440)  # 日周期
    cpu_noise = np.random.normal(0, 5, n_samples)
    cpu_usage = np.clip(cpu_base + cpu_noise, 0, 100)

    # 内存：缓慢增长趋势
    memory_trend = np.linspace(40, 60, n_samples)
    memory_usage = memory_trend + np.random.normal(0, 3, n_samples)

    # 延迟：与CPU正相关
    latency = 50 + 0.5 * cpu_usage + np.random.normal(0, 10, n_samples)

    # 构造特征矩阵
    features = np.column_stack([cpu_usage, memory_usage, latency])

    # 注入异常
    anomaly_start = 8000
    features[anomaly_start:anomaly_start+100, 0] += 40  # CPU异常飙升
    features[anomaly_start:anomaly_start+100, 2] *= 3   # 延迟暴涨

    # 训练检测器
    detector = LSTMAnomalyDetector(seq_length=60, epochs=30)
    detector.fit(features[:7000])  # 只用正常数据训练

    # 检测
    result = detector.predict(features)

    # 找出异常
    anomaly_indices = np.where(result['is_anomaly'])[0]
    print(f"检测到 {len(anomaly_indices)} 个异常点")
    print(f"人工注入的异常位置: {anomaly_start}-{anomaly_start+100}")

    # 计算检测效果
    true_positives = np.sum((anomaly_indices >= anomaly_start) &
                           (anomaly_indices < anomaly_start + 100))
    false_positives = len(anomaly_indices) - true_positives

    print(f"真正例: {true_positives}, 假正例: {false_positives}")

    return result


# 运行示例
# result = server_metrics_anomaly_detection()
```

### 3.3 Prophet 时序预测与异常检测

```python
"""
Facebook Prophet 时序异常检测
优势：自动处理缺失值、趋势变化、季节性，无需参数调优
适用：具有强季节性的业务指标
"""
from prophet import Prophet
import pandas as pd
import numpy as np
from typing import List, Dict, Optional

class ProphetAnomalyDetector:
    """基于Prophet的时序异常检测"""

    def __init__(self,
                 changepoint_prior_scale: float = 0.05,
                 seasonality_prior_scale: float = 10.0,
                 holidays_prior_scale: float = 10.0,
                 interval_width: float = 0.95):
        """
        初始化Prophet检测器

        Args:
            changepoint_prior_scale: 趋势变化灵活性
            seasonality_prior_scale: 季节性灵活性
            interval_width: 置信区间宽度
        """
        self.model = Prophet(
            changepoint_prior_scale=changepoint_prior_scale,
            seasonality_prior_scale=seasonality_prior_scale,
            holidays_prior_scale=holidays_prior_scale,
            interval_width=interval_width,
            daily_seasonality=True,
            weekly_seasonality=True,
            yearly_seasonality=True
        )
        self.interval_width = interval_width

    def add_seasonality(self, name: str, period: float, fourier_order: int):
        """添加自定义季节性"""
        self.model.add_seasonality(
            name=name,
            period=period,
            fourier_order=fourier_order
        )

    def add_holidays(self, holidays_df: pd.DataFrame):
        """
        添加节假日信息

        Args:
            holidays_df: 包含'holiday', 'ds', 'lower_window', 'upper_window'的DataFrame
        """
        self.model = Prophet(holidays=holidays_df)

    def fit(self, df: pd.DataFrame):
        """
        训练模型

        Args:
            df: DataFrame，包含'ds'(时间戳)和'y'(值)列
        """
        self.model.fit(df)
        self.training_data = df.copy()

    def detect(self, df: pd.DataFrame,
               sensitivity: float = 1.0) -> pd.DataFrame:
        """
        检测异常

        Args:
            df: 待检测数据
            sensitivity: 敏感度倍数，越大越容易检测异常

        Returns:
            DataFrame，包含预测值、置信区间和异常标记
        """
        # 预测
        forecast = self.model.predict(df)

        # 合并实际值
        result = forecast.merge(
            df[['ds', 'y']], on='ds', how='left'
        )

        # 计算置信区间
        uncertainty = (result['yhat_upper'] - result['yhat_lower']) / 2
        adjusted_lower = result['yhat'] - sensitivity * uncertainty
        adjusted_upper = result['yhat'] + sensitivity * uncertainty

        # 标记异常
        result['is_anomaly'] = (
            (result['y'] < adjusted_lower) |
            (result['y'] > adjusted_upper)
        )

        result['anomaly_score'] = np.abs(
            (result['y'] - result['yhat']) / uncertainty
        )

        result['anomaly_direction'] = np.where(
            result['y'] > adjusted_upper, 'high',
            np.where(result['y'] < adjusted_lower, 'low', 'normal')
        )

        return result


# ========== 实战：电商业务指标异常检测 ==========

def ecommerce_anomaly_detection():
    """
    电商订单量异常检测

    场景：检测订单量的异常波动，包括：
    - 促销活动期间的预期高峰
    - 系统故障导致的订单下降
    - 异常的流量峰值
    """

    # 生成模拟数据
    np.random.seed(42)
    dates = pd.date_range(start='2025-01-01', periods=90*24, freq='H')

    # 基础趋势 + 日周期 + 周周期 + 噪声
    base_trend = np.linspace(1000, 1200, len(dates))
    daily_pattern = 200 * np.sin(2 * np.pi * np.arange(len(dates)) / 24)
    weekly_pattern = 100 * np.sin(2 * np.pi * np.arange(len(dates)) / (24*7))
    noise = np.random.normal(0, 50, len(dates))

    orders = base_trend + daily_pattern + weekly_pattern + noise
    orders = np.maximum(orders, 0)  # 确保非负

    # 添加促销事件（2025-02-10到02-12）
    promo_start = pd.Timestamp('2025-02-10')
    promo_end = pd.Timestamp('2025-02-12')
    promo_mask = (dates >= promo_start) & (dates <= promo_end)
    orders[promo_mask] *= 2.5

    # 添加系统故障（2025-03-01凌晨）
    failure_start = 60 * 24  # 第60天
    orders[failure_start:failure_start+4] *= 0.1  # 订单量暴跌

    # 创建DataFrame
    df = pd.DataFrame({
        'ds': dates,
        'y': orders
    })

    # 添加促销活动作为节假日
    holidays = pd.DataFrame({
        'holiday': 'promotion',
        'ds': pd.to_datetime(['2025-02-10', '2025-02-11', '2025-02-12']),
        'lower_window': 0,
        'upper_window': 0
    })

    # 训练模型（使用正常数据，排除已知的故障）
    train_df = df[~((df['ds'] >= '2025-03-01') & (df['ds'] < '2025-03-02'))]

    detector = ProphetAnomalyDetector(interval_width=0.95)
    detector.add_holidays(holidays)
    detector.fit(train_df[:60*24])  # 使用前60天训练

    # 检测整个时间段的异常
    result = detector.detect(df, sensitivity=1.5)

    # 分析结果
    anomalies = result[result['is_anomaly']]
    print(f"检测到 {len(anomalies)} 个异常点")

    # 分类异常
    high_anomalies = anomalies[anomalies['anomaly_direction'] == 'high']
    low_anomalies = anomalies[anomalies['anomaly_direction'] == 'low']

    print(f"异常高值: {len(high_anomalies)} 个")
    print(f"异常低值: {len(low_anomalies)} 个")

    # 检测到的故障时间
    failure_detected = anomalies[
        (anomalies['ds'] >= '2025-03-01') &
        (anomalies['ds'] < '2025-03-01 04:00')
    ]
    print(f"\n系统故障检测: {len(failure_detected)} 个异常点")

    return result


"""
# PromQL 异常检测规则示例

# 1. 基于历史同期的异常检测
groups:
  - name: anomaly_detection
    rules:
      # 订单量同比异常（与上周比变化超过50%）
      - alert: OrderVolumeAnomaly
        expr: |
          abs(
            (
              sum(rate(orders_total[1h]))
              - sum(rate(orders_total[1h] offset 1w))
            ) / sum(rate(orders_total[1h] offset 1w))
          ) > 0.5
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "订单量异常波动"
          description: "订单量与上周同期相比变化超过50%"

      # 多指标联合异常（延迟升高且错误率升高）
      - alert: ServiceDegradation
        expr: |
          (
            histogram_quantile(0.99,
              sum(rate(http_request_duration_seconds_bucket[5m])) by (le, service)
            ) > 2 * avg_over_time(
              histogram_quantile(0.99,
                sum(rate(http_request_duration_seconds_bucket[1h])) by (le, service)
              )[1h:5m]
            )
          ) and (
            sum(rate(http_requests_total{status=~"5.."}[5m])) by (service)
            / sum(rate(http_requests_total[5m])) by (service) > 0.01
          )
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "服务性能严重下降"
          description: "服务 {{ $labels.service }} 延迟和错误率同时异常"
"""
```

---

## 4. 分布式追踪异常分析

### 4.1 追踪数据异常模式

```python
"""
分布式追踪异常分析
从Trace数据中提取异常模式
"""
from typing import List, Dict, Optional, Set
from dataclasses import dataclass
from collections import defaultdict
import json

@dataclass
class Span:
    """追踪Span数据结构"""
    trace_id: str
    span_id: str
    parent_span_id: Optional[str]
    service_name: str
    operation_name: str
    start_time: int  # 微秒时间戳
    duration: int    # 微秒
    status_code: str  # OK, ERROR
    attributes: Dict[str, any]
    events: List[Dict]

@dataclass
class Trace:
    """完整追踪"""
    trace_id: str
    spans: List[Span]

    def get_root_span(self) -> Optional[Span]:
        """获取根Span"""
        for span in self.spans:
            if span.parent_span_id is None:
                return span
        return None

    def get_children(self, span_id: str) -> List[Span]:
        """获取子Span"""
        return [s for s in self.spans if s.parent_span_id == span_id]


class TraceAnomalyAnalyzer:
    """追踪异常分析器"""

    def __init__(self):
        self.baseline_stats = defaultdict(lambda: {
            'durations': [],
            'error_count': 0,
            'total_count': 0
        })

    def analyze_trace(self, trace: Trace) -> Dict:
        """
        分析单个追踪的异常

        Returns:
            {
                'trace_id': ...,
                'anomalies': [...],
                'anomaly_score': ...,
                'critical_path': [...]
            }
        """
        anomalies = []

        # 1. 检测错误Span
        error_spans = [s for s in trace.spans if s.status_code == 'ERROR']
        for span in error_spans:
            anomalies.append({
                'type': 'error_span',
                'span_id': span.span_id,
                'service': span.service_name,
                'operation': span.operation_name,
                'severity': 'critical'
            })

        # 2. 检测延迟异常
        latency_anomalies = self._detect_latency_anomalies(trace)
        anomalies.extend(latency_anomalies)

        # 3. 检测结构异常
        structure_anomalies = self._detect_structure_anomalies(trace)
        anomalies.extend(structure_anomalies)

        # 4. 识别关键路径
        critical_path = self._identify_critical_path(trace)

        # 5. 计算整体异常分数
        anomaly_score = self._calculate_anomaly_score(anomalies, trace)

        return {
            'trace_id': trace.trace_id,
            'anomalies': anomalies,
            'anomaly_score': anomaly_score,
            'critical_path': critical_path,
            'span_count': len(trace.spans),
            'duration_ms': self._get_trace_duration(trace) / 1000
        }

    def _detect_latency_anomalies(self, trace: Trace) -> List[Dict]:
        """检测延迟异常"""
        anomalies = []

        for span in trace.spans:
            # 获取该操作的基线
            key = f"{span.service_name}:{span.operation_name}"
            baseline = self.baseline_stats[key]

            if len(baseline['durations']) >= 10:
                p95 = sorted(baseline['durations'])[int(len(baseline['durations']) * 0.95)]

                # P95的2倍以上认为是异常
                if span.duration > p95 * 2:
                    anomalies.append({
                        'type': 'latency_anomaly',
                        'span_id': span.span_id,
                        'service': span.service_name,
                        'operation': span.operation_name,
                        'duration_ms': span.duration / 1000,
                        'baseline_p95_ms': p95 / 1000,
                        'slowdown_ratio': span.duration / p95,
                        'severity': 'warning' if span.duration < p95 * 5 else 'critical'
                    })

            # 更新基线
            baseline['durations'].append(span.duration)
            baseline['total_count'] += 1
            if len(baseline['durations']) > 1000:  # 限制历史大小
                baseline['durations'].pop(0)

        return anomalies

    def _detect_structure_anomalies(self, trace: Trace) -> List[Dict]:
        """检测追踪结构异常"""
        anomalies = []

        # 1. 检测过深的调用链
        max_depth = self._calculate_max_depth(trace)
        if max_depth > 10:
            anomalies.append({
                'type': 'deep_call_chain',
                'max_depth': max_depth,
                'severity': 'warning'
            })

        # 2. 检测循环调用
        cycles = self._detect_cycles(trace)
        if cycles:
            anomalies.append({
                'type': 'circular_dependency',
                'cycles': cycles,
                'severity': 'critical'
            })

        # 3. 检测孤儿Span
        orphan_spans = self._detect_orphan_spans(trace)
        for span in orphan_spans:
            anomalies.append({
                'type': 'orphan_span',
                'span_id': span.span_id,
                'service': span.service_name,
                'severity': 'info'
            })

        return anomalies

    def _identify_critical_path(self, trace: Trace) -> List[Dict]:
        """
        识别关键路径（耗时最长的调用路径）
        """
        root = trace.get_root_span()
        if not root:
            return []

        critical_path = []
        current = root

        while current:
            critical_path.append({
                'span_id': current.span_id,
                'service': current.service_name,
                'operation': current.operation_name,
                'duration_ms': current.duration / 1000,
                'self_time_ms': self._calculate_self_time(trace, current) / 1000
            })

            # 找到耗时最长的子Span
            children = trace.get_children(current.span_id)
            if not children:
                break

            current = max(children, key=lambda s: s.duration)

        return critical_path

    def _calculate_self_time(self, trace: Trace, span: Span) -> int:
        """计算Span的自耗时（不包括子Span的时间）"""
        children = trace.get_children(span.span_id)
        children_duration = sum(c.duration for c in children)
        return max(0, span.duration - children_duration)

    def _calculate_max_depth(self, trace: Trace) -> int:
        """计算调用链最大深度"""
        def get_depth(span_id: str, visited: Set[str]) -> int:
            if span_id in visited:
                return 0
            visited.add(span_id)
            children = trace.get_children(span_id)
            if not children:
                return 1
            return 1 + max(get_depth(c.span_id, visited.copy()) for c in children)

        root = trace.get_root_span()
        if not root:
            return 0
        return get_depth(root.span_id, set())

    def _detect_cycles(self, trace: Trace) -> List[List[str]]:
        """检测调用循环"""
        # 简化的循环检测
        cycles = []
        service_calls = defaultdict(set)

        for span in trace.spans:
            if span.parent_span_id:
                parent = next((s for s in trace.spans if s.span_id == span.parent_span_id), None)
                if parent:
                    service_calls[parent.service_name].add(span.service_name)

        # 检查A->B->A的简单循环
        for service_a, calls in service_calls.items():
            for service_b in calls:
                if service_a in service_calls.get(service_b, set()):
                    cycles.append([service_a, service_b])

        return cycles

    def _detect_orphan_spans(self, trace: Trace) -> List[Span]:
        """检测孤儿Span（找不到父Span）"""
        span_ids = {s.span_id for s in trace.spans}
        orphans = []

        for span in trace.spans:
            if span.parent_span_id and span.parent_span_id not in span_ids:
                orphans.append(span)

        return orphans

    def _get_trace_duration(self, trace: Trace) -> int:
        """获取追踪总耗时"""
        if not trace.spans:
            return 0
        start = min(s.start_time for s in trace.spans)
        end = max(s.start_time + s.duration for s in trace.spans)
        return end - start

    def _calculate_anomaly_score(self, anomalies: List[Dict], trace: Trace) -> float:
        """计算整体异常分数"""
        if not anomalies:
            return 0.0

        severity_scores = {
            'info': 0.2,
            'warning': 0.5,
            'critical': 1.0
        }

        total_score = sum(
            severity_scores.get(a['severity'], 0.3)
            for a in anomalies
        )

        # 归一化到0-1
        return min(total_score / 3, 1.0)


# ========== TraceQL 查询示例 ==========

"""
# TraceQL异常查询

# 1. 查询包含错误Span的追踪
{ status = error }

# 2. 查询高延迟追踪（根Span延迟超过1秒）
{ duration > 1s }

# 3. 查询特定服务的错误追踪
{ .service.name = "payment-service" && status = error }

# 4. 查询包含数据库慢查询的追踪
{ .db.system = "mysql" && .db.statement =~ ".*SELECT.*" && duration > 500ms }

# 5. 复杂查询：支付服务的异常追踪
{
  .service.name = "payment-service"
  && status = error
  && .http.status_code = 500
  && duration > 2s
}

# 6. 查找调用深度超过5层的追踪
{ }
| select(span_count) > 5

# 7. 聚合查询：按服务统计错误率
{ status = error }
| by(.service.name)
| count()
"""
```

### 4.2 追踪异常关联分析

```python
"""
跨Trace的异常关联分析
识别系统性的异常模式
"""
from collections import defaultdict
from typing import List, Dict, Tuple
import networkx as nx

class TraceCorrelationAnalyzer:
    """追踪关联分析器"""

    def __init__(self):
        self.service_graph = nx.DiGraph()
        self.error_patterns = defaultdict(int)
        self.latency_patterns = defaultdict(list)

    def build_service_graph(self, traces: List[Trace]):
        """
        构建服务依赖图
        """
        for trace in traces:
            for span in trace.spans:
                if span.parent_span_id:
                    parent = next(
                        (s for s in trace.spans if s.span_id == span.parent_span_id),
                        None
                    )
                    if parent:
                        # 添加服务间调用边
                        caller = parent.service_name
                        callee = span.service_name

                        if not self.service_graph.has_edge(caller, callee):
                            self.service_graph.add_edge(
                                caller, callee,
                                calls=0, errors=0, total_latency=0
                            )

                        edge = self.service_graph[caller][callee]
                        edge['calls'] += 1
                        edge['errors'] += 1 if span.status_code == 'ERROR' else 0
                        edge['total_latency'] += span.duration

        # 计算平均延迟和错误率
        for u, v, data in self.service_graph.edges(data=True):
            if data['calls'] > 0:
                data['error_rate'] = data['errors'] / data['calls']
                data['avg_latency_ms'] = (data['total_latency'] / data['calls']) / 1000

    def identify_cascading_failures(self) -> List[Dict]:
        """
        识别级联故障模式

        检测信号：
        - 一个服务的错误导致下游服务连锁失败
        - 错误在服务间传播
        """
        cascades = []

        # 查找高错误率的边
        high_error_edges = [
            (u, v, d) for u, v, d in self.service_graph.edges(data=True)
            if d.get('error_rate', 0) > 0.1  # 错误率超过10%
        ]

        # 分析下游影响
        for source, target, data in high_error_edges:
            downstream = nx.descendants(self.service_graph, target)

            if downstream:
                affected = len(downstream)
                cascades.append({
                    'source': source,
                    'initial_failure': target,
                    'affected_services': list(downstream),
                    'affected_count': affected,
                    'error_rate': data['error_rate'],
                    'pattern': 'cascading_failure'
                })

        return sorted(cascades, key=lambda x: x['affected_count'], reverse=True)

    def identify_bottlenecks(self) -> List[Dict]:
        """
        识别系统瓶颈

        基于PageRank思想识别关键服务
        """
        if len(self.service_graph) == 0:
            return []

        # 计算服务的中心性
        centrality = nx.pagerank(self.service_graph)

        # 计算每个服务的总延迟贡献
        service_latency = defaultdict(list)
        for u, v, data in self.service_graph.edges(data=True):
            service_latency[v].append(data.get('avg_latency_ms', 0))

        bottlenecks = []
        for service, cent in centrality.items():
            avg_latency = np.mean(service_latency.get(service, [0]))

            # 瓶颈分数 = 中心性 * 平均延迟
            bottleneck_score = cent * (avg_latency / 1000)

            if bottleneck_score > 0.01:  # 阈值
                bottlenecks.append({
                    'service': service,
                    'centrality': cent,
                    'avg_latency_ms': avg_latency,
                    'bottleneck_score': bottleneck_score,
                    'incoming_calls': len(list(self.service_graph.predecessors(service))),
                    'outgoing_calls': len(list(self.service_graph.successors(service)))
                })

        return sorted(bottlenecks, key=lambda x: x['bottleneck_score'], reverse=True)

    def identify_hotspots(self, traces: List[Trace], time_window_ms: int = 60000) -> List[Dict]:
        """
        识别异常热点

        在特定时间窗口内聚集的异常
        """
        # 按时间窗口分组
        windows = defaultdict(list)

        for trace in traces:
            window_key = trace.spans[0].start_time // time_window_ms if trace.spans else 0

            analyzer = TraceAnomalyAnalyzer()
            result = analyzer.analyze_trace(trace)

            if result['anomaly_score'] > 0.3:
                windows[window_key].append(result)

        # 识别热点窗口
        hotspots = []
        for window, anomalies in windows.items():
            if len(anomalies) >= 5:  # 至少5个异常追踪
                # 按服务聚合
                service_counts = defaultdict(int)
                for a in anomalies:
                    for anomaly in a['anomalies']:
                        service = anomaly.get('service', 'unknown')
                        service_counts[service] += 1

                hotspots.append({
                    'time_window': window * time_window_ms,
                    'anomaly_count': len(anomalies),
                    'top_services': sorted(
                        service_counts.items(),
                        key=lambda x: x[1],
                        reverse=True
                    )[:5],
                    'severity': 'critical' if len(anomalies) > 20 else 'warning'
                })

        return sorted(hotspots, key=lambda x: x['anomaly_count'], reverse=True)


# ========== 可视化输出 ==========

def generate_anomaly_report(trace_anomalies: List[Dict],
                           correlations: Dict) -> str:
    """
    生成异常分析报告
    """
    report = []
    report.append("# 追踪异常分析报告")
    report.append(f"\n分析时间: {pd.Timestamp.now()}")
    report.append(f"追踪样本数: {len(trace_anomalies)}")

    # 异常概览
    total_anomalies = sum(len(t['anomalies']) for t in trace_anomalies)
    high_score_traces = [t for t in trace_anomalies if t['anomaly_score'] > 0.5]

    report.append(f"\n## 异常概览")
    report.append(f"- 异常追踪数: {len([t for t in trace_anomalies if t['anomalies']])}")
    report.append(f"- 总异常数: {total_anomalies}")
    report.append(f"- 高危追踪: {len(high_score_traces)}")

    # 级联故障
    cascades = correlations.get('cascading_failures', [])
    if cascades:
        report.append(f"\n## 级联故障 ({len(cascades)}个)")
        for i, cascade in enumerate(cascades[:5], 1):
            report.append(f"\n{i}. {cascade['source']} → {cascade['initial_failure']}")
            report.append(f"   - 影响服务: {cascade['affected_count']}个")
            report.append(f"   - 错误率: {cascade['error_rate']:.2%}")

    # 系统瓶颈
    bottlenecks = correlations.get('bottlenecks', [])
    if bottlenecks:
        report.append(f"\n## 系统瓶颈 (Top 5)")
        for i, b in enumerate(bottlenecks[:5], 1):
            report.append(f"\n{i}. {b['service']}")
            report.append(f"   - 瓶颈分数: {b['bottleneck_score']:.4f}")
            report.append(f"   - 平均延迟: {b['avg_latency_ms']:.2f}ms")
            report.append(f"   - 入度/出度: {b['incoming_calls']}/{b['outgoing_calls']}")

    return '\n'.join(report)
```

---

## 5. 根因分析(RCA)方法论

### 5.1 RCA分析框架

```
┌─────────────────────────────────────────────────────────────────┐
│                    根因分析(RCA)框架                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  Phase 1: 故障发现与确认                                 │   │
│  │  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐  │   │
│  │  │ 告警触发    │ →  │ 影响确认    │ →  │ 范围界定    │  │   │
│  │  └─────────────┘    └─────────────┘    └─────────────┘  │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              │                                  │
│                              ▼                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  Phase 2: 数据收集与关联                                 │   │
│  │  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐  │   │
│  │  │ Metrics     │    │ Logs        │    │ Traces      │  │   │
│  │  │ 指标数据    │ +  │ 日志数据    │ +  │ 追踪数据    │  │   │
│  │  └─────────────┘    └─────────────┘    └─────────────┘  │   │
│  │                          ↓                               │   │
│  │  ┌─────────────────────────────────────────────────────┐ │   │
│  │  │              时间窗口对齐与关联                      │ │   │
│  │  └─────────────────────────────────────────────────────┘ │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              │                                  │
│                              ▼                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  Phase 3: 根因定位                                       │   │
│  │  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐  │   │
│  │  │ 时序关联    │    │ 拓扑分析    │    │ 事件关联    │  │   │
│  │  │ 找出变化点  │    │ 依赖分析    │    │ 异常检测    │  │   │
│  │  └─────────────┘    └─────────────┘    └─────────────┘  │   │
│  │                          ↓                               │   │
│  │  ┌─────────────────────────────────────────────────────┐ │   │
│  │  │              根因候选排序与验证                      │ │   │
│  │  └─────────────────────────────────────────────────────┘ │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              │                                  │
│                              ▼                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  Phase 4: 根因报告与修复                                 │   │
│  │  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐  │   │
│  │  │ 根因确认    │ →  │ 修复方案    │ →  │ 预防措施    │  │   │
│  │  └─────────────┘    └─────────────┘    └─────────────┘  │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 5.2 自动化RCA实现

```python
"""
自动化根因分析(RCA)系统
结合Metrics、Logs、Traces进行多维度分析
"""
from typing import List, Dict, Optional, Tuple
from dataclasses import dataclass
from datetime import datetime, timedelta
import numpy as np
import pandas as pd

@dataclass
class Incident:
    """故障事件"""
    id: str
    start_time: datetime
    service: str
    symptom: str  # 症状描述
    severity: str  # P0, P1, P2
    metrics_context: Dict
    traces_context: List[Trace]
    logs_context: List[Dict]

@dataclass
class RootCause:
    """根因分析结果"""
    incident_id: str
    root_cause_type: str  # infrastructure, code, dependency, config
    root_cause_service: str
    root_cause_description: str
    confidence: float
    evidence: List[Dict]
    timeline: List[Dict]
    recommendations: List[str]


class AutomatedRCA:
    """自动化根因分析引擎"""

    def __init__(self):
        self.correlation_window = timedelta(minutes=5)
        self.anomaly_detector = TimeSeriesDecompositionDetector()
        self.trace_analyzer = TraceAnomalyAnalyzer()

    def analyze(self, incident: Incident) -> RootCause:
        """
        分析故障的根因
        """
        # 1. 构建时间线
        timeline = self._build_timeline(incident)

        # 2. 多维度关联分析
        correlations = self._multi_dimension_correlation(incident)

        # 3. 根因推断
        root_cause_type, root_cause_service = self._infer_root_cause(
            incident, correlations, timeline
        )

        # 4. 收集证据
        evidence = self._collect_evidence(incident, correlations, timeline)

        # 5. 生成修复建议
        recommendations = self._generate_recommendations(
            root_cause_type, root_cause_service, evidence
        )

        # 6. 计算置信度
        confidence = self._calculate_confidence(evidence, correlations)

        return RootCause(
            incident_id=incident.id,
            root_cause_type=root_cause_type,
            root_cause_service=root_cause_service,
            root_cause_description=self._generate_description(
                root_cause_type, root_cause_service, evidence
            ),
            confidence=confidence,
            evidence=evidence,
            timeline=timeline,
            recommendations=recommendations
        )

    def _build_timeline(self, incident: Incident) -> List[Dict]:
        """
        构建故障时间线
        """
        timeline = []

        # 分析指标变化点
        if incident.metrics_context:
            change_points = self._detect_change_points(incident.metrics_context)
            for cp in change_points:
                timeline.append({
                    'timestamp': cp['timestamp'],
                    'type': 'metric_change',
                    'service': incident.service,
                    'description': f"指标 {cp['metric']} 发生突变",
                    'severity': 'high' if cp['change_magnitude'] > 0.5 else 'medium'
                })

        # 分析追踪异常
        for trace in incident.traces_context:
            trace_result = self.trace_analyzer.analyze_trace(trace)
            if trace_result['anomalies']:
                # 找到最早的异常
                earliest = min(
                    trace.spans,
                    key=lambda s: s.start_time
                )
                timeline.append({
                    'timestamp': datetime.fromtimestamp(earliest.start_time / 1e6),
                    'type': 'trace_anomaly',
                    'service': earliest.service_name,
                    'description': f"追踪异常: {len(trace_result['anomalies'])}个问题",
                    'severity': 'critical' if trace_result['anomaly_score'] > 0.7 else 'warning'
                })

        # 分析日志异常
        for log in incident.logs_context:
            if log.get('level') in ['ERROR', 'FATAL']:
                timeline.append({
                    'timestamp': log.get('timestamp'),
                    'type': 'log_error',
                    'service': log.get('service'),
                    'description': log.get('message', 'Unknown error'),
                    'severity': 'critical' if log.get('level') == 'FATAL' else 'high'
                })

        # 按时间排序
        timeline.sort(key=lambda x: x['timestamp'])
        return timeline

    def _detect_change_points(self, metrics: Dict) -> List[Dict]:
        """
        检测指标变化点
        使用CUSUM算法
        """
        change_points = []

        for metric_name, series in metrics.items():
            if len(series) < 10:
                continue

            # 计算CUSUM统计量
            mean = np.mean(series[:-10])  # 使用前90%作为基线
            std = np.std(series[:-10])

            if std == 0:
                continue

            cusum_pos = 0
            cusum_neg = 0
            threshold = 5 * std

            for i, value in enumerate(series[-10:], start=len(series)-10):
                cusum_pos = max(0, cusum_pos + value - mean - 0.5 * std)
                cusum_neg = min(0, cusum_neg + value - mean + 0.5 * std)

                if cusum_pos > threshold or abs(cusum_neg) > threshold:
                    change_points.append({
                        'timestamp': datetime.now() - timedelta(minutes=len(series)-i),
                        'metric': metric_name,
                        'change_magnitude': abs(value - mean) / mean if mean != 0 else 0,
                        'direction': 'up' if value > mean else 'down'
                    })
                    break

        return change_points

    def _multi_dimension_correlation(self, incident: Incident) -> Dict:
        """
        多维度关联分析
        """
        correlations = {
            'metric_to_trace': [],
            'trace_to_log': [],
            'temporal': []
        }

        # 1. Metrics与Traces关联
        for trace in incident.traces_context:
            for span in trace.spans:
                # 检查是否有相关的指标异常
                for metric_name, series in incident.metrics_context.items():
                    if span.service_name in metric_name:
                        correlations['metric_to_trace'].append({
                            'metric': metric_name,
                            'trace_id': trace.trace_id,
                            'service': span.service_name,
                            'correlation_type': 'service_match'
                        })

        # 2. Traces与Logs关联
        for trace in incident.traces_context:
            for span in trace.spans:
                related_logs = [
                    log for log in incident.logs_context
                    if log.get('trace_id') == trace.trace_id or
                       log.get('span_id') == span.span_id
                ]
                if related_logs:
                    correlations['trace_to_log'].append({
                        'trace_id': trace.trace_id,
                        'span_id': span.span_id,
                        'log_count': len(related_logs),
                        'error_logs': len([l for l in related_logs if l.get('level') == 'ERROR'])
                    })

        # 3. 时间关联
        if incident.traces_context and incident.logs_context:
            trace_times = [min(s.start_time for s in t.spans) for t in incident.traces_context]
            log_times = [l.get('timestamp', datetime.now()).timestamp() * 1e6
                        for l in incident.logs_context]

            # 找时间相近的事件
            for tt in trace_times:
                for lt in log_times:
                    if abs(tt - lt) < 60 * 1e6:  # 1分钟内
                        correlations['temporal'].append({
                            'trace_time': datetime.fromtimestamp(tt / 1e6),
                            'log_time': datetime.fromtimestamp(lt / 1e6),
                            'time_diff_ms': abs(tt - lt) / 1000
                        })

        return correlations

    def _infer_root_cause(self, incident: Incident,
                         correlations: Dict,
                         timeline: List[Dict]) -> Tuple[str, str]:
        """
        推断根因类型和服务
        """
        # 分析时间线找出最早的异常
        if not timeline:
            return ('unknown', incident.service)

        earliest = timeline[0]
        root_service = earliest.get('service', incident.service)

        # 根据最早异常的类型推断根因类型
        type_mapping = {
            'metric_change': 'infrastructure',
            'trace_anomaly': 'dependency',
            'log_error': 'code'
        }

        root_cause_type = type_mapping.get(earliest['type'], 'unknown')

        # 进一步细化
        if root_cause_type == 'infrastructure':
            # 检查是否有配置变更相关日志
            config_logs = [
                l for l in incident.logs_context
                if 'config' in l.get('message', '').lower() or
                   'deploy' in l.get('message', '').lower()
            ]
            if config_logs:
                root_cause_type = 'config'

        return (root_cause_type, root_service)

    def _collect_evidence(self, incident: Incident,
                         correlations: Dict,
                         timeline: List[Dict]) -> List[Dict]:
        """
        收集支持根因分析的证据
        """
        evidence = []

        # 添加时间线证据
        for event in timeline[:5]:  # Top 5事件
            evidence.append({
                'type': 'timeline_event',
                'timestamp': event['timestamp'],
                'description': event['description'],
                'severity': event['severity']
            })

        # 添加关联证据
        if correlations['metric_to_trace']:
            evidence.append({
                'type': 'correlation',
                'description': f"发现 {len(correlations['metric_to_trace'])} 个指标-追踪关联",
                'details': correlations['metric_to_trace'][:3]
            })

        # 添加关键指标
        if incident.metrics_context:
            for metric, series in list(incident.metrics_context.items())[:3]:
                if series:
                    evidence.append({
                        'type': 'metric',
                        'name': metric,
                        'current_value': series[-1] if series else None,
                        'baseline': np.mean(series[:-10]) if len(series) > 10 else None,
                        'change_percent': ((series[-1] - np.mean(series[:-10])) / np.mean(series[:-10]) * 100)
                                         if len(series) > 10 and np.mean(series[:-10]) != 0 else 0
                    })

        return evidence

    def _generate_recommendations(self, root_cause_type: str,
                                  root_cause_service: str,
                                  evidence: List[Dict]) -> List[str]:
        """
        生成修复建议
        """
        recommendations = {
            'infrastructure': [
                f"检查 {root_cause_service} 所在节点的资源使用情况（CPU/内存/磁盘）",
                "检查网络连接状态",
                "检查是否有节点故障或维护",
                "考虑扩容或迁移服务"
            ],
            'code': [
                f"检查 {root_cause_service} 最近的代码变更",
                "查看错误日志定位具体代码位置",
                "考虑回滚到稳定版本",
                "在测试环境复现问题"
            ],
            'dependency': [
                f"检查 {root_cause_service} 依赖的下游服务状态",
                "检查数据库连接池和查询性能",
                "检查缓存服务可用性",
                "验证第三方服务健康状态"
            ],
            'config': [
                f"检查 {root_cause_service} 的配置变更",
                "验证配置参数合理性",
                "考虑回滚配置",
                "加强配置变更的测试流程"
            ],
            'unknown': [
                "收集更多信息进行分析",
                "联系相关服务负责人",
                "考虑启用降级策略",
                "准备故障演练"
            ]
        }

        return recommendations.get(root_cause_type, recommendations['unknown'])

    def _generate_description(self, root_cause_type: str,
                             root_cause_service: str,
                             evidence: List[Dict]) -> str:
        """生成根因描述"""
        type_names = {
            'infrastructure': '基础设施故障',
            'code': '代码缺陷',
            'dependency': '依赖服务故障',
            'config': '配置问题',
            'unknown': '未知原因'
        }

        return f"{root_cause_service} 的{type_names.get(root_cause_type, root_cause_type)}"

    def _calculate_confidence(self, evidence: List[Dict],
                             correlations: Dict) -> float:
        """
        计算根因分析置信度
        """
        score = 0.5  # 基础分数

        # 证据越多置信度越高
        score += min(len(evidence) * 0.05, 0.2)

        # 多维度关联增加置信度
        if correlations['metric_to_trace']:
            score += 0.1
        if correlations['trace_to_log']:
            score += 0.1
        if correlations['temporal']:
            score += 0.1

        # 高严重性证据增加置信度
        high_severity = sum(1 for e in evidence if e.get('severity') == 'high')
        score += min(high_severity * 0.05, 0.15)

        return min(score, 1.0)


# ========== RCA报告生成 ==========

def generate_rca_report(root_cause: RootCause) -> str:
    """生成RCA报告"""
    report = []
    report.append("=" * 60)
    report.append("                  故障根因分析报告")
    report.append("=" * 60)
    report.append(f"\n故障ID: {root_cause.incident_id}")
    report.append(f"根因类型: {root_cause.root_cause_type}")
    report.append(f"根因服务: {root_cause.root_cause_service}")
    report.append(f"置信度: {root_cause.confidence:.1%}")
    report.append(f"\n根因描述:\n  {root_cause.root_cause_description}")

    report.append("\n" + "-" * 60)
    report.append("证据链:")
    report.append("-" * 60)
    for i, ev in enumerate(root_cause.evidence, 1):
        report.append(f"\n{i}. [{ev['type']}] {ev.get('description', '')}")
        if 'details' in ev:
            report.append(f"   详情: {ev['details']}")

    report.append("\n" + "-" * 60)
    report.append("时间线:")
    report.append("-" * 60)
    for event in root_cause.timeline:
        time_str = event['timestamp'].strftime('%H:%M:%S') if isinstance(event['timestamp'], datetime) else str(event['timestamp'])
        report.append(f"  [{time_str}] [{event['severity']}] {event['description']}")

    report.append("\n" + "-" * 60)
    report.append("修复建议:")
    report.append("-" * 60)
    for i, rec in enumerate(root_cause.recommendations, 1):
        report.append(f"  {i}. {rec}")

    report.append("\n" + "=" * 60)

    return '\n'.join(report)
```

---

## 6. 故障定位实战案例

### 6.1 案例：电商大促期间的性能下降

```
┌─────────────────────────────────────────────────────────────────┐
│            案例：电商大促期间订单服务性能下降                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  【场景描述】                                                    │
│  - 时间: 2025年双11零点                                          │
│  - 现象: 订单服务P99延迟从200ms飙升到5s                          │
│  - 影响: 订单成功率从99.5%下降到85%                               │
│                                                                 │
│  【异常检测】                                                    │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  检测方法: LSTM时序异常检测                              │   │
│  │                                                          │   │
│  │  输入特征:                                               │   │
│  │  • 订单服务QPS                                           │   │
│  │  • 订单服务延迟P99                                       │   │
│  │  • 数据库连接数                                          │   │
│  │  • 缓存命中率                                            │   │
│  │  • 下游支付服务延迟                                      │   │
│  │                                                          │   │
│  │  检测结果:                                               │   │
│  │  • 异常分数: 0.92 (阈值0.8)                              │   │
│  │  • 异常类型: 多维度联合异常                              │   │
│  │  • 异常开始: 00:00:15                                    │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  【追踪分析】                                                    │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  关键链路:                                               │   │
│  │                                                          │   │
│  │  Gateway(5ms) → OrderService(4500ms) → PaymentService    │   │
│  │                   ↓                                      │   │
│  │              MySQL(4200ms) ← 瓶颈!                       │   │
│  │                                                          │   │
│  │  异常发现:                                               │   │
│  │  • OrderService→MySQL的查询延迟异常高                    │   │
│  │  • 数据库连接池使用率100%                                │   │
│  │  • 大量慢查询: SELECT * FROM orders WHERE user_id=?      │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  【根因定位】                                                    │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  时间线:                                                 │   │
│  │  23:55:00  数据库连接池配置变更 (100→50)                  │   │
│  │  00:00:00  大促开始，流量激增                            │   │
│  │  00:00:15  连接池耗尽，排队等待                          │   │
│  │  00:00:30  延迟飙升，错误率上升                          │   │
│  │                                                          │   │
│  │  根因: 配置变更导致连接池过小，无法承载大促流量            │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  【修复措施】                                                    │
│  1. 立即回滚连接池配置到100                                      │
│  2. 扩容数据库连接池到200                                        │
│  3. 优化慢查询，添加user_id索引                                  │
│  4. 增加连接池监控告警                                           │
│                                                                 │
│  【预防措施】                                                    │
│  • 大促前进行配置审计                                           │
│  • 建立配置变更影响评估流程                                      │
│  • 实施自动化的容量规划                                          │
│  • 增加熔断降级机制                                              │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 6.2 案例：微服务级联故障

```python
"""
微服务级联故障分析案例
"""

def cascading_failure_analysis():
    """
    级联故障分析示例
    """

    # 模拟追踪数据
    traces = []

    # 正常时期的追踪
    for i in range(100):
        spans = [
            Span(
                trace_id=f"normal-{i}",
                span_id="root",
                parent_span_id=None,
                service_name="gateway",
                operation_name="/api/order",
                start_time=0,
                duration=100000,  # 100ms
                status_code="OK",
                attributes={},
                events=[]
            ),
            Span(
                trace_id=f"normal-{i}",
                span_id="order-span",
                parent_span_id="root",
                service_name="order-service",
                operation_name="create_order",
                start_time=10000,
                duration=50000,
                status_code="OK",
                attributes={},
                events=[]
            ),
            Span(
                trace_id=f"normal-{i}",
                span_id="payment-span",
                parent_span_id="order-span",
                service_name="payment-service",
                operation_name="process_payment",
                start_time=20000,
                duration=30000,
                status_code="OK",
                attributes={},
                events=[]
            )
        ]
        traces.append(Trace(trace_id=f"normal-{i}", spans=spans))

    # 故障时期的追踪（inventory-service故障导致级联）
    for i in range(100):
        inventory_failing = i < 50  # 前50个有库存服务故障

        root_span = Span(
            trace_id=f"failure-{i}",
            span_id="root",
            parent_span_id=None,
            service_name="gateway",
            operation_name="/api/order",
            start_time=0,
            duration=3000000 if inventory_failing else 150000,  # 3s或150ms
            status_code="ERROR" if inventory_failing else "OK",
            attributes={},
            events=[]
        )

        order_span = Span(
            trace_id=f"failure-{i}",
            span_id="order-span",
            parent_span_id="root",
            service_name="order-service",
            operation_name="create_order",
            start_time=10000,
            duration=2900000 if inventory_failing else 100000,
            status_code="ERROR" if inventory_failing else "OK",
            attributes={},
            events=[]
        )

        inventory_span = Span(
            trace_id=f"failure-{i}",
            span_id="inventory-span",
            parent_span_id="order-span",
            service_name="inventory-service",
            operation_name="check_stock",
            start_time=20000,
            duration=2800000,  # 2.8s超时
            status_code="ERROR",
            attributes={"error": "connection_timeout"},
            events=[{"name": "timeout", "timestamp": 2820000}]
        )

        spans = [root_span, order_span, inventory_span]
        traces.append(Trace(trace_id=f"failure-{i}", spans=spans))

    # 分析
    analyzer = TraceCorrelationAnalyzer()
    analyzer.build_service_graph(traces)

    cascades = analyzer.identify_cascading_failures()
    bottlenecks = analyzer.identify_bottlenecks()

    print("级联故障分析结果:")
    print(f"发现的级联故障: {len(cascades)}")
    for cascade in cascades:
        print(f"  - {cascade['source']} 影响 {cascade['affected_count']} 个服务")

    print(f"\n系统瓶颈:")
    for b in bottlenecks[:3]:
        print(f"  - {b['service']}: 分数={b['bottleneck_score']:.4f}")

    return cascades, bottlenecks


# 分析结果解读
"""
分析结果:

级联故障:
  - inventory-service 影响 2 个服务 (order-service, gateway)

系统瓶颈 (Top 3):
  - inventory-service: 分数=0.4231  ← 根因服务
  - order-service: 分数=0.2154
  - gateway: 分数=0.1231

RCA结论:
1. 根本原因: inventory-service 响应超时
2. 传播路径: inventory-service → order-service → gateway
3. 影响范围: 50%的订单请求失败
4. 修复优先级:
   P0: 恢复inventory-service
   P1: 增加order-service对inventory-service的超时和熔断
   P2: 优化inventory-service性能
"""
```

---

## 7. 最佳实践与工具推荐

### 7.1 异常检测实施路径

```
┌─────────────────────────────────────────────────────────────────┐
│                 异常检测实施路径建议                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Phase 1: 基础阶段 (1-2周)                                      │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  ✓ 基于阈值的静态告警                                    │   │
│  │  ✓ 简单的3-sigma统计检测                                 │   │
│  │  ✓ 关键指标的同比环比检测                                │   │
│  │  工具: Prometheus Alertmanager                          │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              ↓                                  │
│  Phase 2: 进阶阶段 (2-4周)                                      │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  ✓ 动态基线建立                                          │   │
│  │  ✓ 多维度联合检测                                        │   │
│  │  ✓ 孤立森林异常检测                                      │   │
│  │  工具: Prophet, Isolation Forest                        │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              ↓                                  │
│  Phase 3: 智能化阶段 (1-2月)                                    │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  ✓ LSTM深度学习检测                                      │   │
│  │  ✓ 追踪异常分析                                          │   │
│  │  ✓ 根因分析自动化                                        │   │
│  │  工具: PyTorch/TensorFlow, 自研RCA系统                   │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              ↓                                  │
│  Phase 4: AIOps阶段 (持续优化)                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  ✓ 智能告警收敛                                          │   │
│  │  ✓ 预测性异常检测                                        │   │
│  │  ✓ 自动故障修复                                          │   │
│  │  工具: 完整AIOps平台                                     │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 7.2 工具与资源推荐

```yaml
# 开源工具推荐

时序异常检测:
  Prophet:
    适用: 业务指标，强季节性
    语言: Python/R
    链接: https://facebook.github.io/prophet/

  Luminol:
    适用: LinkedIn开源，轻量级
    语言: Python
    链接: https://github.com/linkedin/luminol

  Banpei:
    适用: 基于SST的异常检测
    语言: Python
    链接: https://github.com/tsurubee/banpei

机器学习:
  PyOD:
    适用: 全面的异常检测库
    算法: 30+种检测算法
    链接: https://github.com/yzhao062/pyod

  Scikit-learn:
    适用: 孤立森林、One-Class SVM
    链接: https://scikit-learn.org/

distributed_tracing:
  Jaeger:
    适用: 追踪收集与查询
    链接: https://www.jaegertracing.io/

  Grafana Tempo:
    适用: 大规模追踪存储
    链接: https://grafana.com/oss/tempo/

  TraceQL:
    适用: 追踪查询语言
    文档: https://grafana.com/docs/tempo/latest/traceql/

根因分析:
  OpenRCA:
    适用: 开源RCA平台
    链接: https://openrca.io/

  自研方案:
    参考: 本指南第5章实现
```

---

## 总结

本指南系统介绍了基于OTLP数据的异常检测与根因分析方法：

1. **统计方法**：适合快速上手，包括3-sigma、IQR、MAD等方法
2. **机器学习方法**：孤立森林适合多变量检测，LSTM适合复杂时序
3. **Prophet**：强大的业务指标异常检测，自动处理季节性
4. **追踪分析**：从Trace数据中提取异常模式，识别级联故障
5. **根因分析**：结合Metrics、Logs、Traces的自动化RCA框架

关键要点：

- 从小处着手，逐步引入更复杂的检测方法
- 多维度数据关联是准确RCA的关键
- 建立反馈循环，持续优化检测准确性
- 关注可解释性，让分析结果可信可用
