"""Shared types for pytest fixtures."""

from typing import TypeAlias

from lcalc_registry.config import Settings
from lcalc_registry.service import Registry

RegistryFixture: TypeAlias = tuple[Settings, Registry]
