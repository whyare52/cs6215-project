#!/usr/bin/env bash
# Run one case study, setting it up first if needed, e.g. `./run-case-study.sh deerflow`.
# Arguments after the name go to the driver, as in `./run-case-study.sh deerflow --no-write`.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
name=${1:?usage: ./run-case-study.sh <case study> [driver arguments]}
shift

declare -A VENV=(
  [deerflow]=deerflow [yuxi]=yuxi [aegra]=aegra [aegra_threads]=aegra-d7d80c85
  [aix_db]=aix-db [open_deep_research]=open-deep-research
  [agent_service_toolkit]=agent-service-toolkit
  [executive_ai_assistant]=executive-ai-assistant [kaymen99]=kaymen99
  [agents_from_scratch]=agents-from-scratch
)
if [ -z "${VENV[$name]+x}" ]; then
  echo "unknown case study $name, expected one of ${!VENV[*]}" >&2
  exit 1
fi

"$here/setup-case-studies.sh" "$name"
cd "$here/checker"
python="../case-studies/venvs/${VENV[$name]}/bin/python"

if [ "$name" = aegra_threads ]; then
  # Aegra's run endpoints need Postgres, here a pinned container for the length of the run
  docker run -d --rm --name cs6215-aegra-pg --memory 2g -p 127.0.0.1:55432:5432 \
    -e POSTGRES_USER=user -e POSTGRES_PASSWORD=password -e POSTGRES_DB=aegra \
    pgvector/pgvector:0.8.1-pg18 >/dev/null
  trap 'docker stop cs6215-aegra-pg >/dev/null' EXIT
  # The image's first start listens on TCP only once initialisation is over
  for _ in $(seq 60); do
    docker exec cs6215-aegra-pg pg_isready -q -h 127.0.0.1 -U user && break
    sleep 1
  done
  "$python" -m "drivers.$name" "$@"
else
  exec "$python" -m "drivers.$name" "$@"
fi
