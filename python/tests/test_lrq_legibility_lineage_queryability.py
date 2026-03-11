from __future__ import annotations

import json
from pathlib import Path

from coherence.tools.query_bridge_artifact import query_doc
from coherence.tools.summarize_phase_status import markdown_summary, summarize_doc

ROOT = Path('/workspace/Sophia')
BRIDGE = ROOT / 'bridge'
DOCS = ROOT / 'docs'


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding='utf-8-sig'))


def test_glossary_completeness() -> None:
    glossary = _load(BRIDGE / 'phase_glossary.json')
    required = {
        'telemetry field',
        'projection',
        'pattern donation',
        'branch emergence',
        'discovery corridor',
        'knowledge river',
        'delta',
        'terrace',
        'successor seed',
        'living terrace',
        'background coherence',
        'keep-open',
        'plurality-protect',
        'executive review',
        'canonical integrity',
        'trustPresentationDegraded',
    }
    terms = {row['term'] for row in glossary['terms']}
    assert required.issubset(terms)


def test_lineage_shape_validity() -> None:
    reg = _load(BRIDGE / 'phase_lineage_registry.json')
    required = {
        'phaseId',
        'phaseName',
        'upstreamArtifacts',
        'downstreamArtifacts',
        'preservedConstraints',
        'transformedConcepts',
        'keyStatuses',
        'humanMeaning',
        'operatorQuestionsAnswered',
        'relatedDocs',
        'canonicalBoundaryNote',
    }
    phases = reg['phases']
    assert phases == sorted(phases, key=lambda p: p['phaseId'])
    for phase in phases:
        assert required.issubset(phase)
        assert all(isinstance(phase[k], list) for k in ('upstreamArtifacts', 'downstreamArtifacts', 'preservedConstraints', 'transformedConcepts', 'keyStatuses', 'operatorQuestionsAnswered', 'relatedDocs'))


def test_coherence_memory_trace_determinism() -> None:
    trace = _load(BRIDGE / 'coherence_memory_trace.json')
    rows = trace['trace']
    assert rows == sorted(rows, key=lambda r: r['phaseId'])
    assert len({r['phaseId'] for r in rows}) == len(rows)


def test_query_helper_behavior() -> None:
    doc = {
        'schema': 'demo',
        'metadata': {'canonicalIntegrity': {'status': 'divergent'}, 'trustPresentationDegraded': True},
        'records': [
            {'targetId': 't1', 'sourceId': 's1', 'phaseId': 'BO', 'backgroundStatus': 'keep-open', 'targetPublisherAction': 'watch'},
            {'targetId': 't2', 'sourceId': 's2', 'phaseId': 'BN', 'backgroundStatus': 'background-visible', 'targetPublisherAction': 'docket'},
        ],
    }
    assert len(query_doc(doc, target_id='t1')) == 1
    assert len(query_doc(doc, source_id='s2')) == 1
    assert len(query_doc(doc, phase_id='BO', status='keep-open')) == 1
    assert len(query_doc(doc, requires_exec_review=True)) == 1
    assert len(query_doc(doc, require_divergent_integrity=True)) == 2
    assert len(query_doc(doc, require_trust_presentation_degraded=True)) == 2


def test_summary_helper_behavior() -> None:
    doc = {
        'schema': 'demo',
        'recommendations': [
            {'targetId': 'a', 'phaseId': 'BO', 'backgroundStatus': 'keep-open', 'targetPublisherAction': 'watch'},
            {'targetId': 'b', 'phaseId': 'BO', 'backgroundStatus': 'background-visible', 'targetPublisherAction': 'docket'},
            {'targetId': 'c', 'phaseId': 'BN', 'backgroundStatus': 'plurality-protect', 'targetPublisherAction': 'suppress'},
        ],
    }
    summary = summarize_doc(doc)
    assert summary['totalEntries'] == 3
    assert summary['executiveReviewCount'] == 1
    assert summary['publisherActionCounts'] == {'watch': 1, 'docket': 1, 'suppress': 1}
    md = markdown_summary(summary)
    assert 'Phase status summary' in md
    assert 'BO' in md


def test_worked_example_links_and_boundary_language() -> None:
    worked = (DOCS / 'WORKED_SIGNAL_PATH_EXAMPLE.md').read_text(encoding='utf-8')
    for ref in [
        'bridge/phase_lineage_registry.json',
        'bridge/phase_glossary.json',
        'bridge/coherence_memory_trace.json',
        'bridge/background_coherence_audit.json',
        'bridge/living_terrace_audit.json',
    ]:
        assert ref in worked
        assert (ROOT / ref).exists() or ref.endswith('_audit.json')

    lineage_doc = (DOCS / 'PHASE_LINEAGE_GUIDE.md').read_text(encoding='utf-8').lower()
    assert 'governance transfer' in lineage_doc
    assert 'canon closure' in lineage_doc

    prohibited_claims = ['epoch authority granted', 'civilization settled by decree', 'history resolved permanently']
    for text in [worked.lower(), lineage_doc, json.dumps(_load(BRIDGE / 'phase_lineage_registry.json')).lower()]:
        for phrase in prohibited_claims:
            assert phrase not in text
