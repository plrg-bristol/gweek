import init, { run_gweek } from './pkg/gweek.js';

let ready = false;

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
        try {
            const result = run_gweek(
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
        } catch (err) {
            self.postMessage({ type: 'error', message: err.message || String(err) });
        }
    }
};

initialize();
