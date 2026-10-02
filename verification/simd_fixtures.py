"""Read the SIMD case registry shared with MSBuild."""

from pathlib import Path
import xml.etree.ElementTree as ET

REGISTRY = Path(__file__).parent / "Tests/Fixtures/SIMD/Cases.props"
_cases = ET.parse(REGISTRY).getroot().findall("ItemGroup/SimdCase")
CASES = tuple(case.attrib["Include"] for case in _cases)
POSITIVES = tuple(case.attrib["Include"] for case in _cases if case.attrib["Suite"] == "positive")
NEGATIVES = tuple(case.attrib["Include"] for case in _cases if case.attrib["Suite"] == "negative")
