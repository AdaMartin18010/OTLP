import { NodeSDK } from '@opentelemetry/sdk-node';
import { getNodeAutoInstrumentations } from '@opentelemetry/auto-instrumentations-node';
import { OTLPTraceExporter } from '@opentelemetry/exporter-otlp-http';
import { trace } from '@opentelemetry/api';
import { performance } from 'perf_hooks';

// 热点分析器
class HotspotAnalyzer {
    constructor() {
        this.functionStats = new Map();
        this.tracer = trace.getTracer('atys-demo');
    }

    // 记录函数执行时间
    recordFunctionExecution(funcName, executionTime) {
        if (!this.functionStats.has(funcName)) {
            this.functionStats.set(funcName, {
                count: 0,
                totalTime: 0,
                avgTime: 0,
                maxTime: 0,
                minTime: Infinity
            });
        }

        const stats = this.functionStats.get(funcName);
        stats.count++;
        stats.totalTime += executionTime;
        stats.avgTime = stats.totalTime / stats.count;
        stats.maxTime = Math.max(stats.maxTime, executionTime);
        stats.minTime = Math.min(stats.minTime, executionTime);
    }

    // 分析热点函数
    analyzeHotspots() {
        const hotspots = [];
        
        for (const [funcName, stats] of this.functionStats) {
            // 计算热点分数 (执行次数 * 平均时间)
            const hotspotScore = stats.count * stats.avgTime;
            
            hotspots.push({
                function: funcName,
                score: hotspotScore,
                count: stats.count,
                avgTime: stats.avgTime,
                maxTime: stats.maxTime,
                minTime: stats.minTime
            });
        }

        // 按热点分数排序
        hotspots.sort((a, b) => b.score - a.score);
        
        return hotspots;
    }

    // 生成热点报告
    generateHotspotReport() {
        const hotspots = this.analyzeHotspots();
        const span = this.tracer.startSpan('hotspot_analysis');
        
        try {
            span.setAttributes({
                'hotspot.total_functions': hotspots.length,
                'hotspot.top_hotspot': hotspots[0]?.function || 'none',
                'hotspot.top_score': hotspots[0]?.score || 0
            });

            console.log('\\n🔥 热点函数分析报告:');
            console.log('='.repeat(50));
            
            hotspots.slice(0, 5).forEach((hotspot, index) => {
                console.log(\\n. );
                console.log(   热点分数: );
                console.log(   执行次数: );
                console.log(   平均时间: ms);
                console.log(   最大时间: ms);
                console.log(   最小时间: ms);
                
                span.addEvent('hotspot_identified', {
                    'hotspot.rank': index + 1,
                    'hotspot.function': hotspot.function,
                    'hotspot.score': hotspot.score
                });
            });

            span.setStatus({ code: 1, message: 'Hotspot analysis completed' });
            
        } finally {
            span.end();
        }
    }
}

// 模拟业务函数
function simulateBusinessLogic(analyzer) {
    const functions = [
        'database_query',
        'cache_lookup',
        'http_request',
        'data_processing',
        'file_io'
    ];

    // 模拟多次函数调用
    for (let i = 0; i < 100; i++) {
        const funcName = functions[Math.floor(Math.random() * functions.length)];
        const startTime = performance.now();
        
        // 模拟函数执行时间
        const executionTime = Math.random() * 50 + 10; // 10-60ms
        const endTime = performance.now();
        
        analyzer.recordFunctionExecution(funcName, executionTime);
        
        // 添加一些延迟
        if (i % 10 === 0) {
            await new Promise(resolve => setTimeout(resolve, 10));
        }
    }
}

// 主函数
async function main() {
    // 配置 OpenTelemetry
    const sdk = new NodeSDK({
        traceExporter: new OTLPTraceExporter({
            url: 'http://localhost:4318/v1/traces',
        }),
        instrumentations: [getNodeAutoInstrumentations()],
    });

    sdk.start();

    // 创建热点分析器
    const analyzer = new HotspotAnalyzer();

    console.log('🚀 开始 Atys 热点分析演示...');

    // 模拟业务逻辑
    await simulateBusinessLogic(analyzer);

    // 生成热点报告
    analyzer.generateHotspotReport();

    console.log('\\n✅ Atys 热点分析演示完成');
}

// 运行主函数
main().catch(console.error);
