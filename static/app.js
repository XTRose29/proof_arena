const AUTH_TOKEN_KEY = "proofArenaAuthToken";

const preferenceChoices = [
  ["a_way_better", "A way better"],
  ["a_better", "A better"],
  ["no_difference", "No difference"],
  ["b_better", "B better"],
  ["b_way_better", "B way better"],
];

const criteria = [
  ["reuse", "Reuse"],
  ["naming", "Naming"],
  ["documentation", "Documentation"],
  ["proofQuality", "Proof-quality"],
  ["overall", "Overall"],
];

const defaultPreferences = Object.fromEntries(criteria.map(([key]) => [key, null]));
const tabItems = [...criteria, ["comment", "Comment"]];

const state = {
  comparison: null,
  activeMode: "reviewer",
  metaPairLoaded: false,
  metaSession: null,
  metaEvaluationA: null,
  metaEvaluationB: null,
  metaChoices: Object.fromEntries(criteria.map(([key]) => [key, null])),
  metaSubmitted: false,
  metaSaveTimer: null,
  metaSavePromise: Promise.resolve(),
  authToken: localStorage.getItem(AUTH_TOKEN_KEY),
  currentUser: null,
  preferences: { ...defaultPreferences },
  completedCriteria: new Set(),
  activeCriterionIndex: 0,
  activeTab: "reuse",
  codePaneFocus: "A",
  vimFocus: "rating",
  waitingForWindowSwitch: false,
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

function setMetaStatus(message, isError = false) {
  const el = document.getElementById("metaStatusText");
  if (!el) {
    return;
  }
  el.textContent = message;
  el.style.color = isError ? "var(--warn)" : "var(--muted)";
}

function escapeHtml(text) {
  return String(text).replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;");
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
  panel.dataset.side = sideLabel;
  panel.querySelector(".panel-side").textContent = sideLabel;
  panel.querySelector(".panel-title").remove();
  panel.querySelector(".panel-meta").remove();
  panel.addEventListener("click", () => setVimFocus(sideLabel));

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
    "Ctrl-W then k/j moves focus up/down. h/l changes the focused row. j/k scrolls code. Space changes criterion. Enter submits.";

  const matrix = document.getElementById("scoreMatrix");
  matrix.querySelectorAll(".matrix-choice").forEach((choiceEl, index) => {
    choiceEl.classList.toggle("selected", index === choiceIndex);
  });
  document.getElementById("submitButton").disabled = !isEvaluationComplete();
  updateRubricReference();
  renderEvaluationTabs();
  updateVimFocusUi();
}

function updateRubricReference() {
  const reference = document.querySelector(".rubric-reference");
  if (!reference) {
    return;
  }

  let hasVisibleLine = false;
  reference.querySelectorAll("[data-rubric]").forEach((line) => {
    const isActive = line.dataset.rubric === state.activeTab;
    line.classList.toggle("hidden", !isActive);
    hasVisibleLine = hasVisibleLine || isActive;
  });
  reference.classList.toggle("hidden", !hasVisibleLine);
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

function showTabByIndex(index) {
  const sectionCount = tabItems.length;
  const nextIndex = (index + sectionCount) % sectionCount;
  if (nextIndex === criteria.length) {
    showCommentTab();
    return;
  }
  showCriterionTab(nextIndex);
}

function cycleCriterion(direction = 1) {
  const currentIndex = state.activeTab === "comment" ? criteria.length : state.activeCriterionIndex;
  showTabByIndex(currentIndex + direction);
}

function setVimFocus(region) {
  state.vimFocus = region;
  state.waitingForWindowSwitch = false;
  if (region === "A" || region === "B") {
    state.codePaneFocus = region;
  }
  updateVimFocusUi();
}

function updateVimFocusUi() {
  document.querySelectorAll(".vim-focused").forEach((el) => el.classList.remove("vim-focused"));
  if (state.vimFocus === "criteria") {
    document.getElementById("evaluationTabs")?.classList.add("vim-focused");
    return;
  }
  if (state.vimFocus === "rating") {
    const target = state.activeTab === "comment" ? "commentPanel" : "evaluationLayout";
    document.getElementById(target)?.classList.add("vim-focused");
    return;
  }
  const sideLabel = state.vimFocus === "A" || state.vimFocus === "B" ? state.vimFocus : state.codePaneFocus;
  document.querySelector(`.panel[data-side="${sideLabel}"]`)?.classList.add("vim-focused");
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
      setVimFocus("criteria");
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
  state.activeTab = "reuse";
  state.codePaneFocus = "A";
  state.vimFocus = "rating";
  state.waitingForWindowSwitch = false;
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
  updateVimFocusUi();
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
  state.metaPairLoaded = false;
  state.metaSession = null;
  state.metaEvaluationA = null;
  state.metaEvaluationB = null;
  state.metaChoices = Object.fromEntries(criteria.map(([key]) => [key, null]));
  state.metaSubmitted = false;
  localStorage.removeItem(AUTH_TOKEN_KEY);
  document.getElementById("accountCardTitle").textContent = "Google Login";
  document.getElementById("googleLoginMount").classList.remove("hidden");
  document.getElementById("accountCompact").classList.add("hidden");
  document.getElementById("arenaGrid").innerHTML = '<article class="panel loading-panel">Log in with Google to see a proof comparison.</article>';
  document.getElementById("metaResults").classList.add("hidden");
  setMetaStatus("");
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
    document.getElementById("arenaGrid").innerHTML = '<article class="panel loading-panel">Log in with Google to see a proof comparison.</article>';
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

function setArenaMode(mode) {
  state.activeMode = mode;
  const reviewerActive = mode === "reviewer";
  document.getElementById("reviewerWorkspace").classList.toggle("hidden", !reviewerActive);
  document.getElementById("metaReviewerWorkspace").classList.toggle("hidden", reviewerActive);
  document.getElementById("reviewerModeButton").classList.toggle("active", reviewerActive);
  document.getElementById("metaReviewerModeButton").classList.toggle("active", !reviewerActive);
  setStatus("");

  if (!reviewerActive && state.currentUser) {
    loadRandomMetaReview().catch((error) => setMetaStatus(error.message, true));
  }
}

async function loadRandomMetaReview(force = false) {
  if (!state.currentUser) {
    throw new Error("Log in with Google to generate a meta-review pair.");
  }
  if (state.metaPairLoaded && !force) {
    return;
  }
  const nextButton = document.getElementById("metaNextButton");
  const submitButton = document.getElementById("metaSubmitButton");
  nextButton.disabled = true;
  submitButton.disabled = true;
  try {
    if (force && state.metaSession && !state.metaSubmitted) {
      await saveMetaDraft();
    }
    setMetaStatus("Loading two evaluations of the same submission…");
    const query = state.metaSession ? `?excludeSessionId=${state.metaSession}` : "";
    const result = await fetchJson(`/api/meta-review/random${query}`, { method: "POST" });
    renderMetaReview(result);
    state.metaPairLoaded = true;
    setMetaStatus("Choose which evaluation is better for every rubric and overall. Each choice saves automatically.");
  } finally {
    nextButton.disabled = false;
  }
}

function renderLeanSource(container, source) {
  container.innerHTML = "";
  const syntaxState = { blockCommentDepth: 0 };
  source.split("\n").forEach((text, index) => {
    container.appendChild(createCodeLine({ lineNumber: index + 1, text }, syntaxState));
  });
}

function createMetaEvaluationCell(item, summary = "") {
  const cell = document.createElement("div");
  cell.className = "meta-evaluation-cell";
  cell.setAttribute("role", "cell");
  const verdict = document.createElement("span");
  verdict.className = `meta-verdict ${item.verdict}`;
  verdict.textContent = item.verdict.replace("_", " ");
  const reason = document.createElement("p");
  reason.textContent = item.reason;
  cell.append(verdict, reason);
  if (summary) {
    const takeaway = document.createElement("p");
    takeaway.className = "meta-summary";
    takeaway.textContent = `Takeaway: ${summary}`;
    cell.appendChild(takeaway);
  }
  return cell;
}

function renderMetaVoteButtons(criterionKey) {
  const cell = document.createElement("div");
  cell.className = "meta-vote-cell";
  cell.setAttribute("role", "cell");
  cell.setAttribute("aria-label", `Vote for ${criterionKey}`);
  [["a", "A"], ["tie", "Tie"], ["b", "B"]].forEach(([choice, label]) => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "meta-vote-button";
    button.textContent = label;
    button.dataset.criterion = criterionKey;
    button.dataset.choice = choice;
    const selected = state.metaChoices[criterionKey] === choice;
    button.classList.toggle("selected", selected);
    button.setAttribute("aria-pressed", String(selected));
    button.disabled = state.metaSubmitted;
    button.addEventListener("click", () => chooseMetaCriterion(criterionKey, choice));
    cell.appendChild(button);
  });
  return cell;
}

function renderMetaEvaluationTable(evaluationA, evaluationB) {
  const table = document.getElementById("metaEvaluationTable");
  table.innerHTML = "";
  const header = document.createElement("div");
  header.className = "meta-table-row meta-table-header";
  header.setAttribute("role", "row");
  ["Rubric", "Evaluation A", "Evaluation B", "Your vote"].forEach((label) => {
    const cell = document.createElement("div");
    cell.setAttribute("role", "columnheader");
    cell.textContent = label;
    header.appendChild(cell);
  });
  table.appendChild(header);

  criteria.forEach(([clientKey, label]) => {
    const apiKey = clientKey === "proofQuality" ? "proof_quality" : clientKey;
    const row = document.createElement("div");
    row.className = "meta-table-row";
    row.setAttribute("role", "row");
    const rubric = document.createElement("div");
    rubric.className = "meta-rubric-cell";
    rubric.setAttribute("role", "rowheader");
    rubric.textContent = label;
    const summaryA = clientKey === "overall" ? evaluationA.summary : "";
    const summaryB = clientKey === "overall" ? evaluationB.summary : "";
    row.append(
      rubric,
      createMetaEvaluationCell(evaluationA[apiKey], summaryA),
      createMetaEvaluationCell(evaluationB[apiKey], summaryB),
      renderMetaVoteButtons(clientKey),
    );
    table.appendChild(row);
  });
}

function metaVoteCount() {
  return criteria.filter(([key]) => Boolean(state.metaChoices[key])).length;
}

function updateMetaProgress() {
  const count = metaVoteCount();
  document.getElementById("metaProgress").textContent = state.metaSubmitted ? "Submitted · pair locked" : `${count} of ${criteria.length} votes`;
  document.getElementById("metaSubmitButton").disabled = state.metaSubmitted || count !== criteria.length;
}

function metaDraftPayload() {
  return {
    choices: state.metaChoices,
    reason: document.getElementById("metaSelectionReason").value.trim(),
  };
}

async function saveMetaDraft() {
  if (!state.metaSession || state.metaSubmitted) {
    return;
  }
  if (state.metaSaveTimer) {
    window.clearTimeout(state.metaSaveTimer);
    state.metaSaveTimer = null;
  }
  const sessionId = state.metaSession;
  const payload = metaDraftPayload();
  setMetaStatus("Saving draft…");
  state.metaSavePromise = state.metaSavePromise.catch(() => {}).then(async () => {
    await fetchJson(`/api/meta-review/${sessionId}/draft`, {
      method: "PUT",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(payload),
    });
    if (state.metaSession === sessionId) {
      setMetaStatus("Draft saved. Submit when all five rubric votes are ready.");
    }
  });
  await state.metaSavePromise;
}

function queueMetaDraftSave() {
  if (state.metaSaveTimer) {
    window.clearTimeout(state.metaSaveTimer);
  }
  state.metaSaveTimer = window.setTimeout(() => {
    saveMetaDraft().catch((error) => setMetaStatus(error.message, true));
  }, 450);
}

function chooseMetaCriterion(criterionKey, choice) {
  if (state.metaSubmitted) {
    return;
  }
  state.metaChoices[criterionKey] = choice;
  renderMetaEvaluationTable(state.metaEvaluationA, state.metaEvaluationB);
  updateMetaProgress();
  queueMetaDraftSave();
}

function renderMetaReview(result) {
  state.metaSession = result.sessionId;
  state.metaEvaluationA = result.a;
  state.metaEvaluationB = result.b;
  state.metaChoices = Object.fromEntries(criteria.map(([key]) => [key, result.draft?.choices?.[key] || null]));
  state.metaSubmitted = Boolean(result.submitted);
  const results = document.getElementById("metaResults");
  document.getElementById("metaProofHeading").textContent = result.source.title;
  renderLeanSource(document.getElementById("metaProofPreview"), result.source.proof);
  const selectionReason = document.getElementById("metaSelectionReason");
  selectionReason.value = result.draft?.reason || "";
  selectionReason.disabled = state.metaSubmitted;
  renderMetaEvaluationTable(result.a, result.b);
  updateMetaProgress();
  results.classList.remove("hidden");
}

async function submitMetaReview() {
  if (!state.metaSession) {
    throw new Error("No evaluation pair is available yet.");
  }
  if (metaVoteCount() !== criteria.length) {
    throw new Error("Vote on all five rubric rows before submitting.");
  }
  document.getElementById("metaSubmitButton").disabled = true;
  await saveMetaDraft();
  await fetchJson(`/api/meta-review/${state.metaSession}/selection`, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(metaDraftPayload()),
  });
  state.metaSubmitted = true;
  document.getElementById("metaSelectionReason").disabled = true;
  renderMetaEvaluationTable(state.metaEvaluationA, state.metaEvaluationB);
  updateMetaProgress();
  setMetaStatus("Submitted. This evaluation pair is now permanently locked.");
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
    throw new Error("Select ratings for all five criteria before submitting.");
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
  cycleCriterion(-1);
}

function moveCriterion(direction) {
  cycleCriterion(direction);
}

function scrollCodePane(sideLabel, direction) {
  const codeViewer = document.querySelector(`.code-viewer[data-side="${sideLabel}"]`);
  if (!codeViewer) {
    return;
  }
  const amount = Math.max(120, codeViewer.clientHeight * 0.65);
  codeViewer.scrollBy({ top: amount * direction, behavior: "smooth" });
}

function handleWindowSwitch(key) {
  if (key === "k") {
    if (state.vimFocus === "rating") {
      setVimFocus("criteria");
    } else if (state.vimFocus === "A" || state.vimFocus === "B") {
      setVimFocus("rating");
    }
    return true;
  }
  if (key === "j") {
    if (state.vimFocus === "criteria") {
      setVimFocus("rating");
    } else if (state.vimFocus === "rating") {
      setVimFocus(state.codePaneFocus);
    }
    return true;
  }
  return false;
}

function handleHorizontalShortcut(direction) {
  if (state.vimFocus === "criteria") {
    cycleCriterion(direction);
    return;
  }
  if (state.vimFocus === "rating") {
    shiftChoice(direction);
    return;
  }
  if (state.vimFocus === "A" || state.vimFocus === "B") {
    setVimFocus(direction < 0 ? "A" : "B");
  }
}

function handleKeyboardShortcuts(event) {
  if (state.activeMode !== "reviewer") {
    return;
  }
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
  const key = event.key.toLowerCase();

  if (event.ctrlKey && key === "w") {
    event.preventDefault();
    state.waitingForWindowSwitch = true;
    setStatus("Ctrl-W: k=focus up, j=focus down");
    return;
  }

  if (state.waitingForWindowSwitch) {
    event.preventDefault();
    state.waitingForWindowSwitch = false;
    if (handleWindowSwitch(key)) {
      setStatus("");
    }
    return;
  }

  if (event.key === "ArrowLeft") {
    event.preventDefault();
    handleHorizontalShortcut(-1);
  } else if (event.key === "ArrowRight") {
    event.preventDefault();
    handleHorizontalShortcut(1);
  } else if (event.key === "ArrowUp") {
    event.preventDefault();
    handleWindowSwitch("k");
  } else if (event.key === "ArrowDown") {
    event.preventDefault();
    handleWindowSwitch("j");
  } else if (event.key === "Enter") {
    event.preventDefault();
    submitEvaluation().catch((error) => setStatus(error.message, true));
  } else if (event.key === " ") {
    event.preventDefault();
    cycleCriterion(1);
  } else if (event.key === "Backspace") {
    event.preventDefault();
    goToPreviousCriterion();
  } else if (event.key === "Escape") {
    event.preventDefault();
    state.waitingForWindowSwitch = false;
    state.vimFocus = null;
    updateVimFocusUi();
    setStatus("");
  } else if (key === "h") {
    event.preventDefault();
    handleHorizontalShortcut(-1);
  } else if (key === "l") {
    event.preventDefault();
    handleHorizontalShortcut(1);
  } else if (key === "j") {
    if (state.vimFocus === "A" || state.vimFocus === "B") {
      event.preventDefault();
      scrollCodePane(state.vimFocus, 1);
    }
  } else if (key === "k") {
    if (state.vimFocus === "A" || state.vimFocus === "B") {
      event.preventDefault();
      scrollCodePane(state.vimFocus, -1);
    }
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
  setArenaMode("reviewer");
  document.getElementById("evaluationTabs").addEventListener("click", () => setVimFocus("criteria"));
  document.getElementById("evaluationLayout").addEventListener("click", () => setVimFocus("rating"));
  document.getElementById("commentPanel").addEventListener("click", (event) => {
    event.stopPropagation();
    setVimFocus("rating");
  });
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
  document.getElementById("reviewerModeButton").addEventListener("click", () => setArenaMode("reviewer"));
  document.getElementById("metaReviewerModeButton").addEventListener("click", () => setArenaMode("meta"));
  document.getElementById("metaNextButton").addEventListener("click", () => {
    loadRandomMetaReview(true).catch((error) => setMetaStatus(error.message, true));
  });
  document.getElementById("metaSubmitButton").addEventListener("click", () => {
    submitMetaReview().catch((error) => setMetaStatus(error.message, true));
  });
  document.getElementById("metaSelectionReason").addEventListener("input", queueMetaDraftSave);
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
