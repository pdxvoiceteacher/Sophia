FROM python:3.11-slim

WORKDIR /app

# Copy project
COPY . /app

# Install python deps (assumes you use python/ as editable package)
RUN python -m pip install -U pip && \
    python -m pip install -e ./python && \
    python -m pip install -e "./ucc[dev]" && \
    python -m pip install fastapi uvicorn

ENV PYTHONPATH=/app/python/src
ENV KONOMI_API_KEY=devkey

EXPOSE 8000
CMD ["python", "-m", "uvicorn", "konomi.api.app:app", "--host", "0.0.0.0", "--port", "8000"]