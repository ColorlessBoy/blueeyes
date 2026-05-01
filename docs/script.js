const redCount = document.querySelector("#red-count");
const quietNights = document.querySelector("#quiet-nights");
const redCountValue = document.querySelector("#red-count-value");
const quietNightsValue = document.querySelector("#quiet-nights-value");
const statusText = document.querySelector("#model-status");
const worldTrack = document.querySelector("#world-track");
const ruleChip = document.querySelector("#rule-chip");

function dotList(count) {
  return Array.from({ length: count }, () => '<span class="dot"></span>').join("");
}

function renderWorlds() {
  const r = Number(redCount.value);
  const k = Number(quietNights.value);

  redCountValue.textContent = String(r);
  quietNightsValue.textContent = String(k);
  ruleChip.textContent = `${k} < totalRed`;

  worldTrack.innerHTML = "";

  for (let total = 1; total <= 8; total += 1) {
    const eliminated = total <= k;
    const actual = total === r;
    const item = document.createElement("div");
    item.className = ["world", eliminated ? "eliminated" : "", actual ? "actual" : ""]
      .filter(Boolean)
      .join(" ");

    const label = eliminated ? "已排除" : actual ? "实际世界" : "仍可能";
    item.innerHTML = `
      <strong>${total}</strong>
      <span class="dots" aria-hidden="true">${dotList(total)}</span>
      <small>${label}</small>
    `;
    worldTrack.appendChild(item);
  }

  const seenByRed = r - 1;
  const decisive = k >= seenByRed;
  const tooLate = k >= r;
  const message = tooLate
    ? `若实际有 ${r} 个红眼者，第 ${r} 晚应已离开；继续安静会与这个实际世界冲突。`
    : decisive
      ? `红眼者看到 ${seenByRed} 个红眼者；经过 ${k} 个安静夜晚后，totalRed = ${seenByRed} 的分支已被排除，所以能推出自己是红眼者。`
      : `红眼者看到 ${seenByRed} 个红眼者；目前只排除了 totalRed ≤ ${k} 的世界，还不足以推出自己的颜色。`;

  statusText.textContent = message;
}

redCount.addEventListener("input", renderWorlds);
quietNights.addEventListener("input", renderWorlds);

renderWorlds();
