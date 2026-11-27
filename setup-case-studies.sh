#!/usr/bin/env bash
# Clone the case-study applications into case-studies/apps/ and make their venvs in
# case-studies/venvs/. With no arguments it sets up every subject, otherwise only the named
# ones, e.g. `./setup-case-studies.sh deerflow yuxi`. A step whose clone, worktree or venv already
# exists is skipped, so the script can be rerun.
set -euo pipefail

cd "$(dirname "$0")/case-studies"
S=apps
V=venvs
R=requirements

clone() { # url dir [git clone flags]
  local url=$1 dir=$2
  shift 2
  [ -d "$S/$dir" ] || git clone "$@" "$url" "$S/$dir"
}

worktree() { # repo dir commit
  [ -d "$S/$2" ] || git -C "$S/$1" worktree add --detach "../$2" "$3"
}

venv() { # name python requirements [uv pip install flags]
  local name=$1 py=$2 req=$3
  shift 3
  [ -d "$V/$name" ] && return
  uv venv -p "$py" "$V/$name"
  VIRTUAL_ENV="$V/$name" uv pip install -r "$R/$req" "$@"
}

deerflow() {
  if [ ! -d "$S/deer-flow" ]; then
    clone https://github.com/bytedance/deer-flow deer-flow
    git -C "$S/deer-flow" fetch --shallow-since=2026-04-20 origin main
    git -C "$S/deer-flow" checkout 00a90bb
  fi
  worktree deer-flow deer-flow-2e05f38 2e05f38
  worktree deer-flow deer-flow-da174dfd da174dfd
  worktree deer-flow deer-flow-fixed c0da2782
  venv deerflow 3.12 deerflow.txt
  venv deerflow-fixed 3.12 deerflow-fixed.txt
}

yuxi() {
  if [ ! -d "$S/Yuxi" ]; then
    clone https://github.com/xerrors/Yuxi Yuxi
    git -C "$S/Yuxi" checkout db0dcb0d
  fi
  worktree Yuxi Yuxi-fixed e0c6159c
  venv yuxi 3.12 yuxi.txt \
    --extra-index-url https://download.pytorch.org/whl/cpu --index-strategy unsafe-best-match
}

aegra() {
  if [ ! -d "$S/aegra" ]; then
    clone https://github.com/aegra/aegra aegra
    git -C "$S/aegra" checkout 9438b502
  fi
  worktree aegra aegra-fixed f1f75177
  local v
  for v in aegra aegra-fixed; do
    [ -d "$V/$v" ] && continue
    venv "$v" 3.12 aegra.txt
    VIRTUAL_ENV="$V/$v" uv pip install --no-deps -e "$S/$v/libs/aegra-api"
  done
}

aegra_threads() {
  aegra
  local c
  for c in d7d80c85 e1b2042; do
    if [ ! -d "$S/aegra-$c" ]; then
      git clone "$S/aegra" "$S/aegra-$c"
      git -C "$S/aegra-$c" checkout --detach "$c"
    fi
    [ -d "$V/aegra-$c" ] && continue
    venv "aegra-$c" 3.12 aegra-336.txt
    VIRTUAL_ENV="$V/aegra-$c" uv pip install --no-deps -e "$S/aegra-$c/libs/aegra-api"
  done
}

aix_db() {
  if [ ! -d "$S/Aix-DB" ]; then
    # Skip the LFS files, also on a machine whose git config names git-lfs but lacks the binary
    GIT_LFS_SKIP_SMUDGE=1 clone https://github.com/apconw/Aix-DB Aix-DB \
      -c filter.lfs.process= -c filter.lfs.smudge= -c filter.lfs.required=false
    git -C "$S/Aix-DB" -c filter.lfs.process= checkout -f ac8e14b1
  fi
  [ -d "$S/Aix-DB-fixed" ] ||
    git -C "$S/Aix-DB" -c filter.lfs.process= worktree add --detach ../Aix-DB-fixed fa9ee98b
  venv aix-db 3.12 aix-db.txt
}

open_deep_research() {
  if [ ! -d "$S/open_deep_research" ]; then
    clone https://github.com/langchain-ai/open_deep_research open_deep_research
    git -C "$S/open_deep_research" checkout 1b7d2e8
  fi
  venv open-deep-research 3.12 open-deep-research.txt
}

agent_service_toolkit() {
  if [ ! -d "$S/agent-service-toolkit" ]; then
    clone https://github.com/JoshuaC215/agent-service-toolkit agent-service-toolkit
    git -C "$S/agent-service-toolkit" fetch origin pull/355/head:pr355
    git -C "$S/agent-service-toolkit" checkout 6aabc5e
  fi
  local c
  for c in 54d5e89 1a1da86 a561c88; do
    worktree agent-service-toolkit "agent-service-toolkit-$c" "$c"
  done
  venv agent-service-toolkit 3.12 agent-service-toolkit.txt
}

executive_ai_assistant() {
  if [ ! -d "$S/executive-ai-assistant" ]; then
    clone https://github.com/langchain-ai/executive-ai-assistant executive-ai-assistant
    git -C "$S/executive-ai-assistant" checkout 758db71
  fi
  # The file is a freeze whose pins the resolver rejects (typing-inspection against
  # typing-extensions), so install exactly what it lists
  venv executive-ai-assistant 3.11 executive-ai-assistant.txt --no-deps
}

kaymen99() {
  if [ ! -d "$S/langgraph-email-automation" ]; then
    clone https://github.com/kaymen99/langgraph-email-automation langgraph-email-automation
    git -C "$S/langgraph-email-automation" checkout 9ea0f54
  fi
  venv kaymen99 3.12 kaymen99.txt
}

agents_from_scratch() {
  if [ ! -d "$S/agents-from-scratch" ]; then
    clone https://github.com/langchain-ai/agents-from-scratch agents-from-scratch
    git -C "$S/agents-from-scratch" checkout 603fc7a
  fi
  venv agents-from-scratch 3.12 agents-from-scratch.txt
}

ALL=(deerflow yuxi aegra aegra_threads aix_db open_deep_research agent_service_toolkit
  executive_ai_assistant kaymen99 agents_from_scratch)

for s in "${@:-${ALL[@]}}"; do
  if [[ ! " ${ALL[*]} " == *" $s "* ]]; then
    echo "unknown subject $s, expected one of ${ALL[*]}" >&2
    exit 1
  fi
  echo "== $s"
  "$s"
done
