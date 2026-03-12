const EXAMPLES = {
    coins: `-- Coin change: how many ways to make 20
-- using coins of value 1, 2, or 10?

add :: Nat -> Nat -> Nat
add n m = case m of
    Z -> n
  | S z -> S (add n z).

coin :: Nat
coin = 1 <> 2 <> 10.

change :: Nat -> [Nat]
change n = case n of
    Z -> []
  | S m -> let c = coin in
            exists rest :: Nat.
            add c rest =:= n.
            c : change rest.

change 20.`,

    perm: `-- Generate all permutations of [1,2,3,4,5,6]
-- by non-deterministic insertion

insert :: Nat -> [Nat] -> [Nat]
insert x xs = case xs of
                  [] -> [x]
                | (z:zs) -> ((x : z : zs) <> (z : insert x zs)).

perm :: [Nat] -> [Nat]
perm xs = case xs of
               [] -> []
            |  (z:zs) -> insert z (perm zs).

perm [1,2,3,4,5,6].`,

    pythagorean: `-- Find Pythagorean triples where c = 5

add :: Nat -> Nat -> Nat
add n m = case m of
    Z -> n
  | S z -> S (add n z).

mult :: Nat -> Nat -> Nat
mult n m = case m of
    Z -> Z
  | S z -> add n (mult n z).

exists a :: Nat. exists b :: Nat. exists c :: Nat.
add (mult a a) (mult b b) =:= (mult c c).
c =:= 5.
(a, (b, c)).`,

    nqueens: `-- Solve N-Queens for a 7x7 board

neq :: Nat -> Nat -> Nat
neq a b = case a of
    Z -> (case b of
        Z -> fail
      | S n -> 0)
  | S m -> (case b of
        Z -> 0
      | S n -> neq m n).

add :: Nat -> Nat -> Nat
add n m = case m of
    Z -> n
  | S z -> S (add n z).

safe :: Nat -> Nat -> [Nat] -> Nat
safe q d rest = case rest of
    [] -> 0
  | (r:rs) -> case neq (add q d) r of
        Z -> (case neq (add r d) q of
            Z -> safe q (S d) rs
          | S n -> fail)
      | S n -> fail.

revappend :: [Nat] -> [Nat] -> [Nat]
revappend xs ys = case xs of
    [] -> ys
  | (z:zs) -> revappend zs (z : ys).

queens :: [Nat] -> [Nat] -> [Nat] -> [Nat]
queens skipped rest placed = case rest of
    [] -> (case skipped of
        [] -> placed
      | (y:ys) -> fail)
  | (q:qs) ->
      (case safe q 1 placed of
         Z -> (let remaining = revappend skipped qs in
               case remaining of
                 [] -> (q : placed)
               | (y:ys) -> queens [] remaining (q : placed))
       | S n -> fail)
      <>
      (queens (q : skipped) qs placed).

queens [] [1,2,3,4,5,6,7] [].`,

    fair: `-- Fair search demo: find 42 in an infinite stream
-- DFS would diverge here; Fair finds it.

f :: Nat -> Nat
f n = n <> f (n + 1).

let y = (f 0) in y =:= 42. y.`,

    hello: `-- Simple existential quantification

hello :: [Nat] -> [Nat]
hello xs = exists ys :: [Nat]. case ys of
                [] -> [4]
              | (z:zs) -> [5].

hello [1, 2, 3].`,
};

const editor = document.getElementById('editor');
const output = document.getElementById('output');
const runBtn = document.getElementById('run-btn');
const status = document.getElementById('status');
const exampleSelect = document.getElementById('examples');

let worker = null;
let running = false;
let startTime = 0;

function escapeHtml(text) {
    const div = document.createElement('div');
    div.textContent = text;
    return div.innerHTML;
}

function formatOutput(raw) {
    return raw.split('\n').map(line => {
        if (line.startsWith('>>>')) {
            return `<span class="summary-line">${escapeHtml(line)}</span>`;
        } else if (line.startsWith('Parse error') || line.startsWith('Type error')) {
            return `<span class="error">${escapeHtml(line)}</span>`;
        } else {
            return escapeHtml(line);
        }
    }).join('\n');
}

function getStrategy() {
    return document.querySelector('input[name="strategy"]:checked').value;
}

function setRunning(isRunning) {
    running = isRunning;
    if (isRunning) {
        runBtn.textContent = 'STOP';
        runBtn.classList.add('running');
    } else {
        runBtn.textContent = 'RUN';
        runBtn.classList.remove('running');
    }
}

function spawnWorker() {
    const w = new Worker('worker.js', { type: 'module' });

    w.onmessage = (e) => {
        if (e.data.type === 'ready') {
            runBtn.disabled = false;
            output.innerHTML = '<span style="color: var(--text-dim)">Ready. Write some gweek and hit RUN.</span>';
            status.textContent = 'Ready';
        } else if (e.data.type === 'result') {
            const elapsed = ((performance.now() - startTime) / 1000).toFixed(2);
            output.innerHTML = formatOutput(e.data.result);
            status.textContent = `Completed in ${elapsed}s`;
            setRunning(false);
        } else if (e.data.type === 'error') {
            output.innerHTML = `<span class="error">${escapeHtml(e.data.message)}</span>`;
            status.textContent = 'Error';
            setRunning(false);
        }
    };

    w.onerror = (e) => {
        output.innerHTML = `<span class="error">Worker error: ${escapeHtml(e.message || String(e))}</span>`;
        status.textContent = 'Error';
        setRunning(false);
    };

    return w;
}

function stopExecution() {
    if (worker) {
        worker.terminate();
        worker = null;
    }
    const elapsed = ((performance.now() - startTime) / 1000).toFixed(2);
    output.innerHTML += '\n<span class="error">>>> interrupted after ' + elapsed + 's</span>';
    status.textContent = `Interrupted after ${elapsed}s`;
    setRunning(false);

    // Respawn worker for next run
    worker = spawnWorker();
}

function runCode() {
    if (running) {
        stopExecution();
        return;
    }

    const source = editor.value;
    if (!source.trim()) {
        output.innerHTML = '<span class="error">No source code.</span>';
        return;
    }

    if (!worker) {
        worker = spawnWorker();
    }

    setRunning(true);
    output.innerHTML = '<span class="loading">Evaluating...</span>';
    status.textContent = 'Running...';
    startTime = performance.now();

    worker.postMessage({
        type: 'run',
        source,
        strategy: getStrategy(),
        optimize: document.getElementById('flag-optimize').checked,
        noOccursCheck: document.getElementById('flag-no-occurs').checked,
        eagerVars: document.getElementById('flag-eager').checked,
        strict: document.getElementById('flag-strict').checked,
        firstOnly: document.getElementById('flag-first').checked,
        timeoutSecs: parseInt(document.getElementById('flag-timeout').value, 10) || 30,
    });
}

// Event listeners
runBtn.addEventListener('click', runCode);

editor.addEventListener('keydown', (e) => {
    if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
        e.preventDefault();
        runCode();
    }

    if (e.key === 'Tab') {
        e.preventDefault();
        const start = editor.selectionStart;
        const end = editor.selectionEnd;
        editor.value = editor.value.substring(0, start) + '    ' + editor.value.substring(end);
        editor.selectionStart = editor.selectionEnd = start + 4;
    }
});

exampleSelect.addEventListener('change', () => {
    const key = exampleSelect.value;
    if (key && EXAMPLES[key]) {
        editor.value = EXAMPLES[key];
        output.innerHTML = '<span style="color: var(--text-dim)">Example loaded. Hit RUN to execute.</span>';
    }
    exampleSelect.value = '';
});

// Init
editor.value = EXAMPLES.coins;
worker = spawnWorker();
