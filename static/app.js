const state = {
  comparison: null,
  panels: {
    left: null,
    right: null,
  },
};

const scoreFields = [
  ["clarity", "Clarity"],
  ["conciseness", "Conciseness"],
  ["idiomaticStructure", "Idiomatic Structure"],
  ["fidelityToNl", "Fidelity to NL Proof"],
  ["overall", "Overall"],
];

const leanKeywords = new Set([
  "abbrev",
  "axiom",
  "by",
  "class",
  "def",
  "do",
  "else",
  "example",
  "have",
  "if",
  "import",
  "in",
  "inductive",
  "instance",
  "lemma",
  "let",
  "match",
  "noncomputable",
  "namespace",
  "open",
  "private",
  "section",
  "set_option",
  "structure",
  "theorem",
  "variable",
  "where",
]);

const leanBuiltins = new Set([
  "Prop",
  "Set",
  "Type",
  "True",
  "False",
  "Nat",
  "Int",
  "String",
  "Fin",
  "MetricSpace",
]);

const leanTactics = new Set([
  "aesop",
  "apply",
  "assumption",
  "calc",
  "constructor",
  "exact",
  "have",
  "induction",
  "intro",
  "omega",
  "rcases",
  "refine",
  "repeat",
  "ring",
  "rw",
  "rfl",
  "simp",
  "simpa",
]);

async function fetchJson(url, options = {}) {
  const response = await fetch(url, options);
  const data = await response.json();
  if (!response.ok) {
    throw new Error(data.error || "Request failed");
  }
  return data;
}

function setStatus(message, isError = false) {
  const el = document.getElementById("statusText");
  el.textContent = message;
  el.style.color = isError ? "var(--warn)" : "var(--muted)";
}

function buildSummary(summary) {
  const card = document.getElementById("summaryCard");
  const topQuestions = summary.questions
    .slice(0, 5)
    .map((question) => `<li>${question.title} (${question.proof_count} proofs)</li>`)
    .join("");
  card.innerHTML = `
    <h2>Dataset Snapshot</h2>
    <p>${summary.counts.questions} questions, ${summary.counts.proofs} proofs, ${summary.counts.nodes} nodes, ${summary.counts.evaluations} saved evaluations.</p>
    <ul>${topQuestions}</ul>
  `;
}

function makeScoreOptions(select) {
  for (let value = 1; value <= 5; value += 1) {
    const option = document.createElement("option");
    option.value = String(value);
    option.textContent = `${value} / 5`;
    if (value === 3) {
      option.selected = true;
    }
    select.appendChild(option);
  }
}

function escapeHtml(text) {
  return text
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;");
}

function highlightToken(token) {
  if (leanKeywords.has(token)) {
    return `<span class="tok-keyword">${token}</span>`;
  }
  if (leanTactics.has(token)) {
    return `<span class="tok-tactic">${token}</span>`;
  }
  if (leanBuiltins.has(token) || /^[A-Z][A-Za-z0-9_'.]*$/.test(token)) {
    return `<span class="tok-type">${token}</span>`;
  }
  return token;
}

function highlightLeanCode(text) {
  const escaped = escapeHtml(text);
  const commentIndex = escaped.indexOf("--");
  const codePart = commentIndex >= 0 ? escaped.slice(0, commentIndex) : escaped;
  const commentPart = commentIndex >= 0 ? escaped.slice(commentIndex) : "";

  const placeholders = [];
  let working = codePart.replace(/"([^"\\]|\\.)*"/g, (match) => {
    const key = `__STRING_${placeholders.length}__`;
    placeholders.push(`<span class="tok-string">${match}</span>`);
    return key;
  });

  working = working.replace(/(?<![\w'])((?:0x[0-9A-Fa-f]+)|(?:\d+(?:\.\d+)?))\b/g, (_, token) => {
    return `<span class="tok-number">${token}</span>`;
  });

  working = working.replace(/[:][=]|=>|->|←|→|↦|:=|≤|≥|≠|∧|∨|¬|∀|∃|λ|\|>/g, (token) => {
    return `<span class="tok-operator">${token}</span>`;
  });

  working = working.replace(/\b[A-Za-z_][A-Za-z0-9_']*\b/g, (token) => {
    if (token.startsWith("__STRING_")) {
      return token;
    }
    return highlightToken(token);
  });

  placeholders.forEach((value, index) => {
    working = working.replace(`__STRING_${index}__`, value);
  });

  if (!commentPart) {
    return working || " ";
  }
  return `${working}<span class="tok-comment">${commentPart}</span>`;
}

function createCodeLine(line, sideState, selectedValueEl) {
  const row = document.createElement("div");
  row.className = "code-line";
  row.dataset.lineNumber = String(line.lineNumber);

  const num = document.createElement("span");
  num.className = "code-line-number";
  num.textContent = String(line.lineNumber);

  const text = document.createElement("span");
  text.className = "code-line-text";
  text.innerHTML = highlightLeanCode(line.text || " ");

  row.append(num, text);
  row.addEventListener("click", () => {
    sideState.selectedLine = {
      lineNumber: line.lineNumber,
      selectedText: line.text,
    };
    selectedValueEl.textContent = String(line.lineNumber);
    row.parentElement.querySelectorAll(".code-line").forEach((node) => {
      node.classList.toggle("selected", node === row);
    });
  });
  return row;
}

function renderLineComments(listEl, sideState) {
  const template = document.getElementById("lineCommentTemplate");
  listEl.innerHTML = "";
  sideState.lineComments.forEach((entry, index) => {
    const node = template.content.firstElementChild.cloneNode(true);
    node.querySelector(".comment-line").textContent = `Line ${entry.lineNumber}`;
    node.querySelector(".comment-snippet").textContent = entry.selectedText;
    node.querySelector(".comment-text").textContent = entry.comment;
    node.querySelector("[data-action='remove-line-comment']").addEventListener("click", () => {
      sideState.lineComments.splice(index, 1);
      renderLineComments(listEl, sideState);
    });
    listEl.appendChild(node);
  });
}

function panelMeta(entity) {
  if (entity.kind === "proof") {
    return `${entity.question_title} | ${entity.source_path}${entity.author ? ` | ${entity.author}` : ""}`;
  }
  return `${entity.question_title} | ${entity.name} | ${entity.node_type} | ${entity.source_path}${entity.author ? ` | ${entity.author}` : ""}`;
}

function renderPanel(side, entity) {
  const template = document.getElementById("panelTemplate");
  const panel = template.content.firstElementChild.cloneNode(true);
  const sideState = {
    entity,
    selectedLine: null,
    lineComments: [],
  };
  state.panels[side] = sideState;

  panel.querySelector(".panel-side").textContent = side;
  panel.querySelector(".panel-title").textContent = entity.kind === "proof" ? entity.title : entity.name;
  panel.querySelector(".panel-meta").textContent = panelMeta(entity);

  const selectedLineValue = panel.querySelector(".selected-line-value");
  const codeViewer = panel.querySelector(".code-viewer");
  entity.lines.forEach((line) => {
    codeViewer.appendChild(createCodeLine(line, sideState, selectedLineValue));
  });

  panel.querySelectorAll("select[data-score]").forEach(makeScoreOptions);

  const lineCommentTextarea = panel.querySelector("[data-role='line-comment']");
  const lineCommentList = panel.querySelector(".line-comment-list");
  panel.querySelector("[data-action='add-line-comment']").addEventListener("click", () => {
    if (!sideState.selectedLine) {
      setStatus(`Select a ${entity.kind} line before adding a line comment.`, true);
      return;
    }
    const comment = lineCommentTextarea.value.trim();
    if (!comment) {
      setStatus("Write a line comment before adding it.", true);
      return;
    }
    sideState.lineComments.push({
      lineNumber: sideState.selectedLine.lineNumber,
      selectedText: sideState.selectedLine.selectedText,
      comment,
    });
    lineCommentTextarea.value = "";
    renderLineComments(lineCommentList, sideState);
    setStatus(`Added a line comment on ${side} line ${sideState.selectedLine.lineNumber}.`);
  });

  return panel;
}

function collectSidePayload(side, panelEl) {
  const sideState = state.panels[side];
  const scores = {};
  panelEl.querySelectorAll("select[data-score]").forEach((select) => {
    scores[select.dataset.score] = Number(select.value);
  });
  return {
    kind: sideState.entity.kind,
    entityId: sideState.entity.id,
    scores,
    generalComment: panelEl.querySelector("[data-role='general-comment']").value.trim(),
    lineComments: sideState.lineComments,
  };
}

async function submitEvaluation() {
  const arena = document.getElementById("arenaGrid");
  const panels = [...arena.querySelectorAll(".panel")].filter((panel) => !panel.classList.contains("loading-panel"));
  if (panels.length !== 2) {
    setStatus("Load a comparison before submitting.", true);
    return;
  }
  const [leftPanel, rightPanel] = panels;
  const payload = {
    mode: state.comparison.mode,
    left: collectSidePayload("left", leftPanel),
    right: collectSidePayload("right", rightPanel),
  };
  const result = await fetchJson("/api/evaluations", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(payload),
  });
  await loadSummary();
  await loadComparison();
  setStatus(`Saved evaluation #${result.sessionId}. Loaded a new pair.`);
}

function renderComparison(comparison) {
  state.comparison = comparison;
  const arena = document.getElementById("arenaGrid");
  arena.innerHTML = "";
  arena.appendChild(renderPanel("left", comparison.left));
  arena.appendChild(renderPanel("right", comparison.right));

  const submitWrap = document.createElement("div");
  submitWrap.className = "submit-wrap";
  const button = document.createElement("button");
  button.className = "submit-button";
  button.textContent = "Submit Evaluation";
  button.addEventListener("click", async () => {
    try {
      await submitEvaluation();
    } catch (error) {
      setStatus(error.message, true);
    }
  });
  submitWrap.appendChild(button);
  arena.appendChild(submitWrap);
}

async function loadSummary() {
  const summary = await fetchJson("/api/summary");
  buildSummary(summary);
}

async function loadComparison() {
  const mode = document.getElementById("modeSelect").value;
  setStatus("Loading comparison...");
  const comparison = await fetchJson(`/api/comparison?mode=${encodeURIComponent(mode)}`);
  renderComparison(comparison);
  setStatus("Comparison loaded.");
}

async function main() {
  document.getElementById("loadButton").addEventListener("click", async () => {
    try {
      await loadComparison();
    } catch (error) {
      setStatus(error.message, true);
    }
  });

  try {
    await loadSummary();
    await loadComparison();
  } catch (error) {
    setStatus(error.message, true);
  }
}

main();
