const AUTH_TOKEN_KEY = "proofArenaAuthToken";

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

const defaultPreferences = Object.fromEntries(criteria.map(([key]) => [key, "no_difference"]));

const state = {
  comparison: null,
  authToken: localStorage.getItem(AUTH_TOKEN_KEY),
  currentUser: null,
  preferences: { ...defaultPreferences },
  activeCriterionIndex: 0,
  googleReady: false,
  googleInitAttempts: 0,
  profileDialogOpen: false,
};

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

function renderPanel(sideLabel, entity) {
  const template = document.getElementById("panelTemplate");
  const panel = template.content.firstElementChild.cloneNode(true);
  panel.querySelector(".panel-side").textContent = sideLabel;
  panel.querySelector(".panel-title").remove();
  panel.querySelector(".panel-meta").remove();

  const codeViewer = panel.querySelector(".code-viewer");
  entity.lines.forEach((line) => {
    codeViewer.appendChild(createCodeLine(line));
  });
  return panel;
}

function updateCriterionUi() {
  const [criterionKey, criterionLabel] = criteria[state.activeCriterionIndex];
  const choiceIndex = preferenceChoices.findIndex(([value]) => value === state.preferences[criterionKey]);
  document.getElementById("criterionTitle").textContent = criterionLabel;
  document.getElementById("criterionProgress").textContent = `${state.activeCriterionIndex + 1} / ${criteria.length}`;
  document.getElementById("criterionHint").textContent =
    state.activeCriterionIndex === criteria.length - 1
      ? "Use Left/Right to adjust the final row. Press Enter to submit this evaluation and load the next pair."
      : "Use Left/Right to choose how strongly you lean toward A or B. Press Enter to confirm this row.";

  const matrix = document.getElementById("scoreMatrix");
  matrix.querySelectorAll(".matrix-choice").forEach((choiceEl, index) => {
    choiceEl.classList.toggle("selected", index === choiceIndex);
  });
  document.getElementById("prevCriterionButton").disabled = state.activeCriterionIndex === 0;
}

function renderScoreMatrix() {
  const matrix = document.getElementById("scoreMatrix");
  matrix.innerHTML = "";

  const [criterionKey, criterionLabel] = criteria[state.activeCriterionIndex];
  const row = document.createElement("div");
  row.className = "matrix-row matrix-row-single";

  const criterion = document.createElement("div");
  criterion.className = "matrix-criterion matrix-criterion-single";
  criterion.innerHTML = `<span class="minor-label">Criterion</span><strong>${criterionLabel}</strong>`;
  row.appendChild(criterion);

  preferenceChoices.forEach(([value, label], index) => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "matrix-choice";
    button.dataset.index = String(index);
    button.dataset.value = value;
    button.innerHTML = `
      <span class="matrix-choice-key">${index + 1}</span>
      <span class="matrix-choice-label">${label}</span>
    `;
    button.addEventListener("click", () => {
      state.preferences[criterionKey] = value;
      updateCriterionUi();
    });
    row.appendChild(button);
  });

  matrix.appendChild(row);
  updateCriterionUi();
}

function resetEvaluationForm() {
  state.preferences = { ...defaultPreferences };
  state.activeCriterionIndex = 0;
  document.getElementById("generalComment").value = "";
  renderScoreMatrix();
}

function renderComparison(comparison) {
  state.comparison = comparison;
  resetEvaluationForm();

  const arena = document.getElementById("arenaGrid");
  arena.innerHTML = "";
  arena.appendChild(renderPanel("A", comparison.a));
  arena.appendChild(renderPanel("B", comparison.b));
  document.getElementById("comparisonModeLabel").textContent = comparison.modeLabel;
  document.getElementById("questionTitleLabel").textContent = comparison.a.question_title || comparison.b.question_title || "Unknown question";
}

function setCurrentUser(user, token) {
  state.currentUser = user;
  if (token) {
    state.authToken = token;
    localStorage.setItem(AUTH_TOKEN_KEY, token);
  }
  document.getElementById("accountCardTitle").textContent = "Account";
  document.getElementById("googleLoginMount").classList.add("hidden");
  document.getElementById("accountCompactName").textContent = user.displayName;
  document.getElementById("accountCompactEmail").textContent = user.email;
  document.getElementById("accountCompact").classList.remove("hidden");
  populateProfileForm(user);
}

function clearCurrentUser() {
  state.currentUser = null;
  state.authToken = null;
  localStorage.removeItem(AUTH_TOKEN_KEY);
  document.getElementById("accountCardTitle").textContent = "Google Login";
  document.getElementById("googleLoginMount").classList.remove("hidden");
  document.getElementById("accountCompact").classList.add("hidden");
}

function populateProfileForm(user) {
  document.getElementById("profileEmail").value = user.email || "";
  document.getElementById("profileDisplayName").value = user.displayName || "";
  document.getElementById("profileAffiliation").value = user.affiliation || "";
  document.getElementById("profileExperienceLevel").value = user.experienceLevel || "";
}

function openProfileDialog() {
  if (!state.currentUser) {
    setStatus("Log in with Google first.", true);
    return;
  }
  populateProfileForm(state.currentUser);
  document.getElementById("profileDialog").showModal();
  state.profileDialogOpen = true;
}

function closeProfileDialog() {
  document.getElementById("profileDialog").close();
  state.profileDialogOpen = false;
}

function logout() {
  if (state.profileDialogOpen) {
    closeProfileDialog();
  }
  clearCurrentUser();
  setStatus("");
}

async function saveProfile(event) {
  event.preventDefault();
  if (!state.currentUser) {
    throw new Error("Log in with Google first.");
  }
  const payload = {
    displayName: document.getElementById("profileDisplayName").value.trim(),
    affiliation: document.getElementById("profileAffiliation").value.trim(),
    experienceLevel: document.getElementById("profileExperienceLevel").value.trim(),
  };
  const result = await fetchJson("/api/me", {
    method: "PUT",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(payload),
  });
  setCurrentUser(result.user);
  closeProfileDialog();
}

async function restoreSession() {
  if (!state.authToken) {
    return;
  }
  try {
    const result = await fetchJson("/api/me");
    setCurrentUser(result.user);
  } catch {
    clearCurrentUser();
  }
}

async function handleGoogleCredentialResponse(response) {
  const result = await fetchJson("/api/auth/google", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ credential: response.credential }),
  });
  setCurrentUser(result.user, result.token);
  setStatus("");
}

function initializeGoogleLogin() {
  if (!window.google?.accounts?.id) {
    state.googleInitAttempts += 1;
    if (state.googleInitAttempts <= 20) {
      window.setTimeout(initializeGoogleLogin, 250);
    } else {
      setStatus("Google Sign-In failed to load.", true);
    }
    return;
  }
  const clientId = document.body.dataset.googleClientId;
  if (!clientId) {
    setStatus("Google Sign-In is not configured.", true);
    return;
  }

  window.google.accounts.id.initialize({
    client_id: clientId,
    callback: (response) => {
      handleGoogleCredentialResponse(response).catch((error) => setStatus(error.message, true));
    },
  });
  window.google.accounts.id.renderButton(document.getElementById("googleLoginMount"), {
    theme: "outline",
    size: "medium",
    shape: "pill",
    text: "signin_with",
    width: 220,
  });
  state.googleReady = true;
}

async function loadComparison() {
  const comparison = await fetchJson("/api/comparison");
  renderComparison(comparison);
  setStatus("");
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
    throw new Error("Log in with Google before submitting.");
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
  setStatus("");
}

function shiftChoice(direction) {
  const [criterionKey] = criteria[state.activeCriterionIndex];
  const currentIndex = preferenceChoices.findIndex(([value]) => value === state.preferences[criterionKey]);
  const nextIndex = Math.max(0, Math.min(preferenceChoices.length - 1, currentIndex + direction));
  state.preferences[criterionKey] = preferenceChoices[nextIndex][0];
  updateCriterionUi();
}

async function advanceCriterion() {
  if (state.activeCriterionIndex < criteria.length - 1) {
    state.activeCriterionIndex += 1;
    renderScoreMatrix();
    return;
  }
  await submitEvaluation();
}

function goToPreviousCriterion() {
  if (state.activeCriterionIndex === 0) {
    return;
  }
  state.activeCriterionIndex -= 1;
  renderScoreMatrix();
}

function handleKeyboardShortcuts(event) {
  if (state.profileDialogOpen) {
    return;
  }
  const tagName = document.activeElement?.tagName;
  if (tagName === "TEXTAREA" || tagName === "INPUT") {
    return;
  }
  if (!state.comparison) {
    return;
  }

  if (event.key === "ArrowLeft") {
    event.preventDefault();
    shiftChoice(-1);
  } else if (event.key === "ArrowRight") {
    event.preventDefault();
    shiftChoice(1);
  } else if (event.key === "Enter") {
    event.preventDefault();
    advanceCriterion().catch((error) => setStatus(error.message, true));
  } else if (event.key === "Backspace") {
    event.preventDefault();
    goToPreviousCriterion();
  } else if (/^[1-5]$/.test(event.key)) {
    const [criterionKey] = criteria[state.activeCriterionIndex];
    state.preferences[criterionKey] = preferenceChoices[Number(event.key) - 1][0];
    updateCriterionUi();
  }
}

async function main() {
  document.body.dataset.googleClientId = "";
  renderScoreMatrix();
  document.getElementById("loadButton").addEventListener("click", () => loadComparison().catch((error) => setStatus(error.message, true)));
  document.getElementById("submitButton").addEventListener("click", () => submitEvaluation().catch((error) => setStatus(error.message, true)));
  document.getElementById("prevCriterionButton").addEventListener("click", goToPreviousCriterion);
  document.getElementById("openProfileButton").addEventListener("click", openProfileDialog);
  document.getElementById("logoutButton").addEventListener("click", logout);
  document.getElementById("closeProfileButton").addEventListener("click", closeProfileDialog);
  document.getElementById("profileForm").addEventListener("submit", (event) => saveProfile(event).catch((error) => setStatus(error.message, true)));
  document.getElementById("profileDialog").addEventListener("close", () => {
    state.profileDialogOpen = false;
  });
  window.addEventListener("keydown", handleKeyboardShortcuts);

  try {
    const config = await fetchJson("/api/auth/config");
    document.body.dataset.googleClientId = config.googleClientId || "";
    initializeGoogleLogin();
    await restoreSession();
    await loadComparison();
  } catch (error) {
    setStatus(error.message, true);
  }
}

main();
