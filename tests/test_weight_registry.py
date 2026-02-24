from __future__ import annotations

from tools.telemetry.weight_registry import WeightRegistry


def test_weight_registry_default_uniform_weight() -> None:
    reg = WeightRegistry()
    assert reg.get_weight("node-any") == 1.0


def test_weight_registry_linear_mode_is_deterministic() -> None:
    nodes = ["n1", "n2", "n3"]
    reg_a = WeightRegistry.for_simulation(node_ids=nodes, mode="linear")
    reg_b = WeightRegistry.for_simulation(node_ids=nodes, mode="linear")
    assert reg_a.get_weight("n1") == 1.0
    assert reg_a.get_weight("n2") == 2.0
    assert reg_a.get_weight("n3") == 3.0
    assert [reg_a.get_weight(n) for n in nodes] == [reg_b.get_weight(n) for n in nodes]


def test_weight_registry_adversarial_mode_minority_high_pattern() -> None:
    nodes = [f"n{i}" for i in range(6)]
    reg = WeightRegistry.for_simulation(node_ids=nodes, mode="adversarial")
    # first third is high-weight minority
    assert reg.get_weight("n0") == 5.0
    assert reg.get_weight("n1") == 5.0
    assert reg.get_weight("n2") == 1.0
    assert reg.get_weight("n5") == 1.0
