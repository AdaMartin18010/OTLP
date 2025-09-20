// Tracezip 压缩技术库
// 基于2025年最新的分布式追踪压缩技术

use opentelemetry::trace::{SpanId, TraceId};
use std::collections::HashMap;
use std::time::{Duration, Instant};

/// Span Retrieval Tree (SRT) 节点
#[derive(Debug, Clone)]
pub struct SRTNode {
    pub span_id: SpanId,
    pub parent_span_id: Option<SpanId>,
    pub operation_name: String,
    pub start_time: u64,
    pub end_time: u64,
    pub attributes: HashMap<String, String>,
    pub children: Vec<SpanId>,
}

/// Span Retrieval Tree (SRT) 结构
#[derive(Debug)]
pub struct SpanRetrievalTree {
    pub trace_id: TraceId,
    pub nodes: HashMap<SpanId, SRTNode>,
    pub root_spans: Vec<SpanId>,
    pub compression_ratio: f64,
    pub created_at: Instant,
}

impl SpanRetrievalTree {
    /// 创建新的SRT
    pub fn new(trace_id: TraceId) -> Self {
        Self {
            trace_id,
            nodes: HashMap::new(),
            root_spans: Vec::new(),
            compression_ratio: 0.0,
            created_at: Instant::now(),
        }
    }

    /// 压缩SRT
    pub fn compress(&mut self) -> Result<Vec<u8>, String> {
        let start_time = Instant::now();
        
        // 序列化SRT为JSON
        let json_data = serde_json::to_string(&self.nodes)
            .map_err(|e| format!("序列化失败: {}", e))?;
        
        // 使用gzip压缩
        let mut encoder = flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::default());
        use std::io::Write;
        encoder.write_all(json_data.as_bytes())
            .map_err(|e| format!("压缩失败: {}", e))?;
        
        let compressed_data = encoder.finish()
            .map_err(|e| format!("完成压缩失败: {}", e))?;
        
        // 计算压缩率
        let original_size = json_data.len();
        let compressed_size = compressed_data.len();
        self.compression_ratio = 1.0 - (compressed_size as f64 / original_size as f64);
        
        let compression_time = start_time.elapsed();
        println!("SRT压缩完成: 原始大小={}字节, 压缩后={}字节, 压缩率={:.2}%, 耗时={:?}", 
                original_size, compressed_size, self.compression_ratio * 100.0, compression_time);
        
        Ok(compressed_data)
    }

    /// 获取trace的统计信息
    pub fn get_trace_stats(&self) -> TraceStats {
        let total_spans = self.nodes.len();
        let max_depth = self.calculate_max_depth();
        let avg_span_duration = self.calculate_avg_duration();
        
        TraceStats {
            trace_id: self.trace_id,
            total_spans,
            max_depth,
            avg_span_duration,
            compression_ratio: self.compression_ratio,
            created_at: self.created_at,
        }
    }

    /// 计算最大深度
    fn calculate_max_depth(&self) -> usize {
        let mut max_depth = 0;
        
        for &root_span_id in &self.root_spans {
            let depth = self.calculate_depth(root_span_id, 0);
            max_depth = max_depth.max(depth);
        }
        
        max_depth
    }

    /// 递归计算深度
    fn calculate_depth(&self, span_id: SpanId, current_depth: usize) -> usize {
        if let Some(node) = self.nodes.get(&span_id) {
            let mut max_child_depth = current_depth;
            for &child_id in &node.children {
                let child_depth = self.calculate_depth(child_id, current_depth + 1);
                max_child_depth = max_child_depth.max(child_depth);
            }
            max_child_depth
        } else {
            current_depth
        }
    }

    /// 计算平均span持续时间
    fn calculate_avg_duration(&self) -> Duration {
        let mut total_duration = 0u64;
        let mut span_count = 0;
        
        for node in self.nodes.values() {
            if node.end_time > node.start_time {
                total_duration += node.end_time - node.start_time;
                span_count += 1;
            }
        }
        
        if span_count > 0 {
            Duration::from_nanos(total_duration / span_count as u64)
        } else {
            Duration::ZERO
        }
    }
}

/// Trace统计信息
#[derive(Debug)]
pub struct TraceStats {
    pub trace_id: TraceId,
    pub total_spans: usize,
    pub max_depth: usize,
    pub avg_span_duration: Duration,
    pub compression_ratio: f64,
    pub created_at: Instant,
}

/// Tracezip压缩器
pub struct TracezipCompressor {
    pub compression_level: u32,
    pub cache_size: usize,
    pub srt_cache: HashMap<TraceId, SpanRetrievalTree>,
}

impl TracezipCompressor {
    /// 创建新的压缩器
    pub fn new(compression_level: u32, cache_size: usize) -> Self {
        Self {
            compression_level,
            cache_size,
            srt_cache: HashMap::new(),
        }
    }

    /// 获取压缩统计信息
    pub fn get_compression_stats(&self) -> CompressionStats {
        let total_traces = self.srt_cache.len();
        let avg_compression_ratio = if total_traces > 0 {
            self.srt_cache.values()
                .map(|srt| srt.compression_ratio)
                .sum::<f64>() / total_traces as f64
        } else {
            0.0
        };
        
        CompressionStats {
            total_traces,
            avg_compression_ratio,
            cache_size: self.srt_cache.len(),
            max_cache_size: self.cache_size,
        }
    }
}

/// 压缩统计信息
#[derive(Debug)]
pub struct CompressionStats {
    pub total_traces: usize,
    pub avg_compression_ratio: f64,
    pub cache_size: usize,
    pub max_cache_size: usize,
}
