FROM python:3.12-slim

WORKDIR /app

COPY proof_arena/requirements.txt /app/requirements.txt
RUN pip install --no-cache-dir -r /app/requirements.txt

COPY . /app

ENV PROOF_ARENA_HOST=0.0.0.0
ENV PROOF_ARENA_PORT=8000
ENV PROOF_ARENA_AUTO_SEED=true

CMD ["python", "-m", "proof_arena.server"]
