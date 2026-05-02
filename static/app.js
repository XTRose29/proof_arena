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

const defaultPreferences = Object.fromEntries(criteria.map(([key]) => [key, null]));
const tabItems = [...criteria, ["comment", "Comment"]];

const state = {
  comparison: null,
  authToken: localStorage.getItem(AUTH_TOKEN_KEY),
  currentUser: null,
  preferences: { ...defaultPreferences },
  completedCriteria: new Set(),
  activeCriterionIndex: 0,
  activeTab: "clarity",
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

const leanBuiltins = new Set([
  "Bool",
  "False",
  "Fin",
  "Float",
  "Int",
  "List",
  "MetricSpace",
  "Nat",
  "Option",
  "Prop",
  "Set",
  "String",
  "Subtype",
  "True",
  "Type",
  "Unit",
]);
const leanTactics = new Set([
  "aesop",
  "apply",
  "assumption",
  "cases",
  "change",
  "constructor",
  "contradiction",
  "decide",
  "exact",
  "ext",
  "field_simp",
  "funext",
  "induction",
  "intro",
  "intros",
  "linarith",
  "norm_num",
  "omega",
  "positivity",
  "r_cases",
  "rcases",
  "refine",
  "ring",
  "rw",
  "rfl",
  "simp",
  "simpa",
  "tauto",
]);
const leanOperators = [
  ":=",
  "=>",
  "->",
  "<-",
  "<=",
  ">=",
  "==",
  "!=",
  "&&",
  "||",
  "|>",
  "←",
  "→",
  "↦",
  "≤",
  "≥",
  "≠",
  "∧",
  "∨",
  "¬",
  "∀",
  "∃",
  "λ",
  "⟨",
  "⟩",
];

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
  if (!el) {
    return;
  }
  el.textContent = message;
  el.style.color = isError ? "var(--warn)" : "var(--muted)";
}

function escapeHtml(text) {
  return text.replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;");
}

function highlightToken(token) {
  const escaped = escapeHtml(token);
  if (leanKeywords.has(token)) {
    return `<span class="tok-keyword">${escaped}</span>`;
  }
  if (leanTactics.has(token)) {
    return `<span class="tok-tactic">${escaped}</span>`;
  }
  if (token === "sorry") {
    return `<span class="tok-sorry">${escaped}</span>`;
  }
  if (leanBuiltins.has(token) || /^[A-Z][A-Za-z0-9_'.]*$/.test(token)) {
    return `<span class="tok-type">${escaped}</span>`;
  }
  return escaped;
}

function highlightLeanCodeSegment(text) {
  const parts = [];
  let index = 0;

  const pushPlain = (value) => {
    parts.push(escapeHtml(value));
  };

  while (index < text.length) {
    const rest = text.slice(index);
    const stringMatch = rest.match(/^"([^"\\]|\\.)*"?/);
    if (stringMatch && rest.startsWith("\"")) {
      parts.push(`<span class="tok-string">${escapeHtml(stringMatch[0])}</span>`);
      index += stringMatch[0].length;
      continue;
    }

    const whitespaceMatch = rest.match(/^\s+/);
    if (whitespaceMatch) {
      pushPlain(whitespaceMatch[0]);
      index += whitespaceMatch[0].length;
      continue;
    }

    const numberMatch = rest.match(/^(0x[0-9A-Fa-f]+|\d+(?:\.\d+)?)/);
    if (numberMatch) {
      parts.push(`<span class="tok-number">${escapeHtml(numberMatch[0])}</span>`);
      index += numberMatch[0].length;
      continue;
    }

    const operator = leanOperators.find((candidate) => rest.startsWith(candidate));
    if (operator) {
      parts.push(`<span class="tok-operator">${escapeHtml(operator)}</span>`);
      index += operator.length;
      continue;
    }

    const identifierMatch = rest.match(/^[A-Za-z_][A-Za-z0-9_']*/);
    if (identifierMatch) {
      parts.push(highlightToken(identifierMatch[0]));
      index += identifierMatch[0].length;
      continue;
    }

    pushPlain(text[index]);
    index += 1;
  }

  return parts.join("");
}

function highlightLeanLine(text, syntaxState) {
  const parts = [];
  let codeStart = 0;
  let index = 0;
  let blockCommentDepth = syntaxState.blockCommentDepth;

  const flushCode = (end) => {
    if (end <= codeStart) {
      return;
    }
    parts.push(highlightLeanCodeSegment(text.slice(codeStart, end)));
  };

  const pushComment = (start, end) => {
    parts.push(`<span class="tok-comment">${escapeHtml(text.slice(start, end))}</span>`);
  };

  while (index < text.length) {
    if (blockCommentDepth > 0) {
      const commentStart = index;
      while (index < text.length && blockCommentDepth > 0) {
        if (text.startsWith("/-", index)) {
          blockCommentDepth += 1;
          index += 2;
          continue;
        }
        if (text.startsWith("-/", index)) {
          blockCommentDepth -= 1;
          index += 2;
          continue;
        }
        index += 1;
      }
      pushComment(commentStart, index);
      codeStart = index;
      continue;
    }

    if (text[index] === "\"") {
      index += 1;
      while (index < text.length) {
        if (text[index] === "\\") {
          index += 2;
          continue;
        }
        if (text[index] === "\"") {
          index += 1;
          break;
        }
        index += 1;
      }
      continue;
    }

    if (text.startsWith("--", index)) {
      flushCode(index);
      pushComment(index, text.length);
      return {
        html: parts.join("") || " ",
        blockCommentDepth,
      };
    }

    if (text.startsWith("/-", index)) {
      flushCode(index);
      blockCommentDepth = 1;
      const commentStart = index;
      index += 2;
      while (index < text.length && blockCommentDepth > 0) {
        if (text.startsWith("/-", index)) {
          blockCommentDepth += 1;
          index += 2;
          continue;
        }
        if (text.startsWith("-/", index)) {
          blockCommentDepth -= 1;
          index += 2;
          continue;
        }
        index += 1;
      }
      pushComment(commentStart, index);
      codeStart = index;
      continue;
    }

    index += 1;
  }

  flushCode(text.length);
  return {
    html: parts.join("") || " ",
    blockCommentDepth,
  };
}

function createCodeLine(line, syntaxState) {
  const row = document.createElement("div");
  row.className = "code-line";

  const num = document.createElement("span");
  num.className = "code-line-number";
  num.textContent = String(line.lineNumber);

  const text = document.createElement("span");
  text.className = "code-line-text";
  const highlighted = highlightLeanLine(line.text || " ", syntaxState);
  text.innerHTML = highlighted.html;
  syntaxState.blockCommentDepth = highlighted.blockCommentDepth;

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
  codeViewer.dataset.side = sideLabel;
  const syntaxState = { blockCommentDepth: 0 };
  entity.lines.forEach((line) => {
    codeViewer.appendChild(createCodeLine(line, syntaxState));
  });
  return panel;
}

function updateCriterionUi() {
  const [criterionKey] = criteria[state.activeCriterionIndex];
  const choiceIndex = preferenceChoices.findIndex(([value]) => value === state.preferences[criterionKey]);
  document.getElementById("criterionHint").textContent =
    state.activeTab === "comment"
      ? "Leave an optional overall comment. Submit is available after all four criteria are selected."
      : "Use Left/Right to choose a rating, Up/Down to change criterion/comment, W/S to scroll A, O/L to scroll B, and Enter to submit.";

  const matrix = document.getElementById("scoreMatrix");
  matrix.querySelectorAll(".matrix-choice").forEach((choiceEl, index) => {
    choiceEl.classList.toggle("selected", index === choiceIndex);
  });
  document.getElementById("submitButton").disabled = !isEvaluationComplete();
  renderEvaluationTabs();
}

function renderScoreMatrix() {
  const matrix = document.getElementById("scoreMatrix");
  matrix.innerHTML = "";

  const [criterionKey] = criteria[state.activeCriterionIndex];
  const row = document.createElement("div");
  row.className = "matrix-row matrix-row-single";

  preferenceChoices.forEach(([value, label], index) => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "matrix-choice";
    button.dataset.index = String(index);
    button.dataset.value = value;
    button.innerHTML = `<span class="matrix-choice-label">${label}</span>`;
    button.addEventListener("click", () => {
      state.preferences[criterionKey] = value;
      state.completedCriteria.add(criterionKey);
      updateCriterionUi();
    });
    row.appendChild(button);
  });

  matrix.appendChild(row);
  updateCriterionUi();
}

function showCriterionTab(index) {
  state.activeCriterionIndex = Math.max(0, Math.min(criteria.length - 1, index));
  state.activeTab = criteria[state.activeCriterionIndex][0];
  document.getElementById("evaluationLayout").classList.add("rating-only");
  document.getElementById("scoreMatrix").classList.remove("hidden");
  document.getElementById("commentPanel").classList.add("hidden");
  renderScoreMatrix();
}

function renderEvaluationTabs() {
  const tabs = document.getElementById("evaluationTabs");
  tabs.innerHTML = "";
  tabItems.forEach(([key, label]) => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "evaluation-tab";
    button.classList.toggle("active", key === state.activeTab);
    button.classList.toggle("complete", key !== "comment" && state.completedCriteria.has(key));
    button.textContent = label;
    button.addEventListener("click", () => {
      if (key === "comment") {
        showCommentTab();
        return;
      }
      const index = criteria.findIndex(([criterionKey]) => criterionKey === key);
      if (index >= 0) {
        showCriterionTab(index);
      }
    });
    tabs.appendChild(button);
  });
}

function isEvaluationComplete() {
  return criteria.every(([key]) => state.completedCriteria.has(key));
}

function showCommentTab() {
  state.activeTab = "comment";
  document.getElementById("evaluationLayout").classList.remove("rating-only");
  document.getElementById("scoreMatrix").classList.add("hidden");
  document.getElementById("commentPanel").classList.remove("hidden");
  updateCriterionUi();
}

function resetEvaluationForm() {
  state.preferences = { ...defaultPreferences };
  state.completedCriteria = new Set();
  state.activeCriterionIndex = 0;
  state.activeTab = "clarity";
  document.getElementById("generalComment").value = "";
  document.getElementById("evaluationLayout").classList.add("rating-only");
  document.getElementById("scoreMatrix").classList.remove("hidden");
  document.getElementById("commentPanel").classList.add("hidden");
  renderScoreMatrix();
}

function renderComparison(comparison) {
  state.comparison = comparison;
  resetEvaluationForm();

  const arena = document.getElementById("arenaGrid");
  arena.innerHTML = "";
  arena.appendChild(renderPanel("A", comparison.a));
  arena.appendChild(renderPanel("B", comparison.b));
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
  state.comparison = null;
  localStorage.removeItem(AUTH_TOKEN_KEY);
  document.getElementById("accountCardTitle").textContent = "Google Login";
  document.getElementById("googleLoginMount").classList.remove("hidden");
  document.getElementById("accountCompact").classList.add("hidden");
  document.getElementById("arenaGrid").innerHTML = '<article class="panel loading-panel">Log in with Google to see a node comparison.</article>';
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
  if (!payload.displayName) {
    throw new Error("Display name is required.");
  }
  state.currentUser = { ...state.currentUser, ...payload };
  document.getElementById("accountCompactName").textContent = state.currentUser.displayName;
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
  await loadComparison();
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
  if (!state.authToken || !state.currentUser) {
    document.getElementById("arenaGrid").innerHTML = '<article class="panel loading-panel">Log in with Google to see a node comparison.</article>';
    return;
  }
  try {
    const comparison = await fetchJson("/api/comparison");
    renderComparison(comparison);
    setStatus("");
  } catch (error) {
    document.getElementById("arenaGrid").innerHTML =
      `<article class="panel loading-panel">${escapeHtml(error.message)}</article>`;
    throw error;
  }
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
    evaluator: {
      displayName: state.currentUser.displayName,
      affiliation: state.currentUser.affiliation || "",
      experienceLevel: state.currentUser.experienceLevel || "",
    },
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
  if (!isEvaluationComplete()) {
    throw new Error("Select ratings for all four criteria before submitting.");
  }
  await fetchJson("/api/evaluations", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(buildEvaluationPayload()),
  });
  await loadComparison();
  setStatus("");
}

function shiftChoice(direction) {
  if (state.activeTab === "comment") {
    return;
  }
  const [criterionKey] = criteria[state.activeCriterionIndex];
  const currentIndex = preferenceChoices.findIndex(([value]) => value === state.preferences[criterionKey]);
  const startingIndex = direction < 0 ? 1 : 3;
  const nextIndex =
    currentIndex === -1
      ? startingIndex
      : Math.max(0, Math.min(preferenceChoices.length - 1, currentIndex + direction));
  state.preferences[criterionKey] = preferenceChoices[nextIndex][0];
  state.completedCriteria.add(criterionKey);
  updateCriterionUi();
}

async function advanceCriterion() {
  if (state.activeTab === "comment") {
    await submitEvaluation();
    return;
  }
  const [criterionKey] = criteria[state.activeCriterionIndex];
  if (!state.preferences[criterionKey]) {
    throw new Error("Choose a rating for this criterion before continuing.");
  }
  state.completedCriteria.add(criterionKey);
  if (state.activeCriterionIndex < criteria.length - 1) {
    state.activeCriterionIndex += 1;
    state.activeTab = criteria[state.activeCriterionIndex][0];
    renderScoreMatrix();
    return;
  }
  showCommentTab();
}

function goToPreviousCriterion() {
  showCriterionTab(state.activeCriterionIndex - 1);
}

function moveCriterion(direction) {
  const sectionCount = criteria.length + 1;
  const currentIndex = state.activeTab === "comment" ? criteria.length : state.activeCriterionIndex;
  const nextIndex = (currentIndex + direction + sectionCount) % sectionCount;
  if (nextIndex === criteria.length) {
    showCommentTab();
    return;
  }
  showCriterionTab(nextIndex);
}

function scrollCodePane(sideLabel, direction) {
  const codeViewer = document.querySelector(`.code-viewer[data-side="${sideLabel}"]`);
  if (!codeViewer) {
    return;
  }
  const amount = Math.max(120, codeViewer.clientHeight * 0.65);
  codeViewer.scrollBy({ top: amount * direction, behavior: "smooth" });
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
  } else if (event.key === "ArrowUp") {
    event.preventDefault();
    moveCriterion(-1);
  } else if (event.key === "ArrowDown") {
    event.preventDefault();
    moveCriterion(1);
  } else if (event.key === "Enter") {
    event.preventDefault();
    submitEvaluation().catch((error) => setStatus(error.message, true));
  } else if (event.key === "Backspace") {
    event.preventDefault();
    goToPreviousCriterion();
  } else if (event.key.toLowerCase() === "w") {
    event.preventDefault();
    scrollCodePane("A", -1);
  } else if (event.key.toLowerCase() === "s") {
    event.preventDefault();
    scrollCodePane("A", 1);
  } else if (event.key.toLowerCase() === "o") {
    event.preventDefault();
    scrollCodePane("B", -1);
  } else if (event.key.toLowerCase() === "l") {
    event.preventDefault();
    scrollCodePane("B", 1);
  }
}

async function toggleFullscreen() {
  const workspace = document.querySelector(".workspace-card");
  if (!document.fullscreenElement) {
    await workspace.requestFullscreen();
  } else {
    await document.exitFullscreen();
  }
}

function updateFullscreenButton() {
  document.getElementById("fullscreenButton").textContent = document.fullscreenElement ? "Exit Full Screen" : "Full Screen";
}

async function main() {
  document.body.dataset.googleClientId = "";
  renderScoreMatrix();
  document.getElementById("loadButton").addEventListener("click", () => loadComparison().catch((error) => setStatus(error.message, true)));
  document.getElementById("submitButton").addEventListener("click", () => submitEvaluation().catch((error) => setStatus(error.message, true)));
  document.getElementById("fullscreenButton").addEventListener("click", () => toggleFullscreen().catch((error) => setStatus(error.message, true)));
  document.getElementById("openProfileButton").addEventListener("click", openProfileDialog);
  document.getElementById("logoutButton").addEventListener("click", logout);
  document.getElementById("closeProfileButton").addEventListener("click", closeProfileDialog);
  document.getElementById("profileForm").addEventListener("submit", (event) => saveProfile(event).catch((error) => setStatus(error.message, true)));
  document.getElementById("profileDialog").addEventListener("close", () => {
    state.profileDialogOpen = false;
  });
  document.addEventListener("fullscreenchange", updateFullscreenButton);
  window.addEventListener("keydown", handleKeyboardShortcuts);

  try {
    const config = await fetchJson("/api/auth/config");
    document.body.dataset.googleClientId = config.googleClientId || "";
    initializeGoogleLogin();
    await restoreSession();
    if (state.currentUser) {
      await loadComparison();
    }
  } catch (error) {
    setStatus(error.message, true);
  }
}

main();
