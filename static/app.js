const AUTH_TOKEN_KEY = "proofArenaAuthToken";

const state = {
  comparison: null,
  authToken: localStorage.getItem(AUTH_TOKEN_KEY),
  currentUser: null,
  preferences: {
    clarity: "no_difference",
    conciseness: "no_difference",
    idiomaticStructure: "no_difference",
    overall: "no_difference",
  },
};

const preferenceChoices = [
  ["a_way_better", "A way better"],
  ["a_better", "A better"],
  ["no_difference", "No difference"],
  ["b_better", "B better"],
  ["b_way_better", "B way better"],
];

const criteria = [
  ["clarity", "Clarity"],
  ["conciseness", "Conciseness"],
  ["idiomaticStructure", "Idiomatic Structure"],
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

const leanBuiltins = new Set(["Prop", "Set", "Type", "True", "False", "Nat", "Int", "String", "Fin", "MetricSpace"]);
const leanTactics = new Set(["aesop", "apply", "assumption", "calc", "constructor", "exact", "have", "induction", "intro", "omega", "rcases", "refine", "repeat", "ring", "rw", "rfl", "simp", "simpa"]);

async function fetchJson(url, options = {}) {
  const headers = new Headers(options.headers || {});
  if (state.authToken) {
    headers.set("Authorization", `Bearer ${state.authToken}`);
  }
  const response = await fetch(url, { ...options, headers });
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

function escapeHtml(text) {
  return text.replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;");
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

function createCodeLine(line) {
  const row = document.createElement("div");
  row.className = "code-line";

  const num = document.createElement("span");
  num.className = "code-line-number";
  num.textContent = String(line.lineNumber);

  const text = document.createElement("span");
  text.className = "code-line-text";
  text.innerHTML = highlightLeanCode(line.text || " ");

  row.append(num, text);
  return row;
}

function panelMeta(entity) {
  if (entity.kind === "proof") {
    return entity.question_title;
  }
  return entity.question_title;
}

function renderPanel(sideLabel, entity) {
  const template = document.getElementById("panelTemplate");
  const panel = template.content.firstElementChild.cloneNode(true);
  panel.querySelector(".panel-side").textContent = sideLabel;
  panel.querySelector(".panel-title").textContent = entity.kind === "proof" ? entity.title : entity.name;
  panel.querySelector(".panel-meta").textContent = panelMeta(entity);

  const codeViewer = panel.querySelector(".code-viewer");
  entity.lines.forEach((line) => {
    codeViewer.appendChild(createCodeLine(line));
  });
  return panel;
}

function renderComparison(comparison) {
  state.comparison = comparison;
  const arena = document.getElementById("arenaGrid");
  arena.innerHTML = "";
  arena.appendChild(renderPanel("A", comparison.a));
  arena.appendChild(renderPanel("B", comparison.b));
  document.getElementById("comparisonModeLabel").textContent = comparison.modeLabel;
}

function renderScoreMatrix() {
  const matrix = document.getElementById("scoreMatrix");
  matrix.innerHTML = "";

  const header = document.createElement("div");
  header.className = "matrix-row matrix-header";
  header.innerHTML = `
    <div>Criterion</div>
    ${preferenceChoices.map(([, label]) => `<div>${label}</div>`).join("")}
  `;
  matrix.appendChild(header);

  criteria.forEach(([key, label]) => {
    const row = document.createElement("div");
    row.className = "matrix-row";
    row.appendChild(Object.assign(document.createElement("div"), { className: "matrix-criterion", textContent: label }));
    preferenceChoices.forEach(([value, choiceLabel]) => {
      const wrapper = document.createElement("label");
      wrapper.className = "matrix-choice";
      const input = document.createElement("input");
      input.type = "radio";
      input.name = `criterion-${key}`;
      input.value = value;
      input.checked = state.preferences[key] === value;
      input.addEventListener("change", () => {
        state.preferences[key] = value;
      });
      const span = document.createElement("span");
      span.textContent = choiceLabel;
      wrapper.append(input, span);
      row.appendChild(wrapper);
    });
    matrix.appendChild(row);
  });
}

function setAuthMode(mode) {
  const loginForm = document.getElementById("loginForm");
  const registerForm = document.getElementById("registerForm");
  document.getElementById("loginTab").classList.toggle("active", mode === "login");
  document.getElementById("registerTab").classList.toggle("active", mode === "register");
  loginForm.classList.toggle("hidden", mode !== "login");
  registerForm.classList.toggle("hidden", mode !== "register");
}

function setCurrentUser(user, token) {
  state.currentUser = user;
  if (token) {
    state.authToken = token;
    localStorage.setItem(AUTH_TOKEN_KEY, token);
  }
  const accountInfo = document.getElementById("accountInfo");
  accountInfo.classList.remove("hidden");
  accountInfo.innerHTML = `
    <strong>${user.displayName}</strong>
    <span>${user.email}</span>
    <span>${user.affiliation || "No affiliation set"}</span>
  `;
  document.getElementById("greetingHeading").textContent = `Hi ${user.displayName}`;
  document.getElementById("accountSummary").innerHTML = `
    <div><strong>Name</strong><span>${user.displayName}</span></div>
    <div><strong>Affiliation</strong><span>${user.affiliation || "Not provided"}</span></div>
    <div><strong>Experience</strong><span>${user.experienceLevel || "Not provided"}</span></div>
  `;
}

async function restoreSession() {
  if (!state.authToken) {
    return;
  }
  try {
    const result = await fetchJson("/api/me");
    setCurrentUser(result.user);
  } catch {
    localStorage.removeItem(AUTH_TOKEN_KEY);
    state.authToken = null;
  }
}

async function handleAuthSubmit(event, mode) {
  event.preventDefault();
  const formData = new FormData(event.currentTarget);
  const payload = Object.fromEntries(formData.entries());
  const endpoint = mode === "login" ? "/api/auth/login" : "/api/auth/register";
  const result = await fetchJson(endpoint, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(payload),
  });
  setCurrentUser(result.user, result.token);
  setStatus(mode === "login" ? "Logged in." : "Account created.");
}

async function loadComparison() {
  setStatus("Loading randomized comparison...");
  const comparison = await fetchJson("/api/comparison");
  renderComparison(comparison);
  setStatus("Random comparison loaded.");
}

function buildEvaluationPayload() {
  return {
    mode: state.comparison.mode,
    a: {
      kind: state.comparison.a.kind,
      entityId: state.comparison.a.entityId,
    },
    b: {
      kind: state.comparison.b.kind,
      entityId: state.comparison.b.entityId,
    },
    preferences: state.preferences,
    generalComment: document.getElementById("generalComment").value.trim(),
  };
}

async function submitEvaluation() {
  if (!state.authToken || !state.currentUser) {
    throw new Error("Login or create an account before submitting.");
  }
  if (!state.comparison) {
    throw new Error("No comparison loaded.");
  }
  const result = await fetchJson("/api/evaluations", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(buildEvaluationPayload()),
  });
  await loadComparison();
  document.getElementById("generalComment").value = "";
  setStatus(`Saved evaluation #${result.sessionId}. Loaded a new random pair.`);
}

async function main() {
  renderScoreMatrix();
  setAuthMode("login");
  document.getElementById("loginTab").addEventListener("click", () => setAuthMode("login"));
  document.getElementById("registerTab").addEventListener("click", () => setAuthMode("register"));
  document.getElementById("loginForm").addEventListener("submit", (event) => handleAuthSubmit(event, "login").catch((error) => setStatus(error.message, true)));
  document.getElementById("registerForm").addEventListener("submit", (event) => handleAuthSubmit(event, "register").catch((error) => setStatus(error.message, true)));
  document.getElementById("loadButton").addEventListener("click", () => loadComparison().catch((error) => setStatus(error.message, true)));
  document.getElementById("submitButton").addEventListener("click", () => submitEvaluation().catch((error) => setStatus(error.message, true)));

  try {
    await restoreSession();
    await loadComparison();
  } catch (error) {
    setStatus(error.message, true);
  }
}

main();
