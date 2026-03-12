import init, { run_gweek, run_gweek_batch } from './pkg/gweek.js';

let ready = false;

// Capture console.error output from console_error_panic_hook
// so we can include the Rust panic message in the error sent to the main thread.
let lastPanic = null;
const origConsoleError = console.error;
console.error = (...args) => {
    lastPanic = args.map(String).join(' ');
    origConsoleError.apply(console, args);
};

async function initialize() {
    await init();
    ready = true;
    self.postMessage({ type: 'ready' });
}

self.onmessage = (e) => {
    if (e.data.type === 'run') {
        if (!ready) {
            self.postMessage({ type: 'error', message: 'WASM not ready' });
            return;
        }
        lastPanic = null;
        try {
            if (e.data.batch) {
                const result = run_gweek_batch(
                    e.data.source,
                    e.data.strategy,
                    e.data.optimize,
                    e.data.noOccursCheck,
                    e.data.eagerVars,
                    e.data.strict,
                    e.data.firstOnly,
                    BigInt(e.data.timeoutSecs)
                );
                self.postMessage({ type: 'result', result });
            } else {
                const onLine = (line) => {
                    self.postMessage({ type: 'line', line });
                };
                const summary = run_gweek(
                    e.data.source,
                    e.data.strategy,
                    e.data.optimize,
                    e.data.noOccursCheck,
                    e.data.eagerVars,
                    e.data.strict,
                    e.data.firstOnly,
                    BigInt(e.data.timeoutSecs),
                    onLine
                );
                self.postMessage({ type: 'done', summary });
            }
        } catch (err) {
            let message;
            if (lastPanic) {
                message = lastPanic;
            } else if (err instanceof WebAssembly.RuntimeError) {
                message = 'Out of memory or stack overflow. Try --first, a shorter timeout, or a different strategy.';
            } else {
                message = err.message || String(err);
            }
            self.postMessage({ type: 'error', message });
        }
    }
};

initialize();
