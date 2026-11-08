"""Derived functors on the Phase 0 kernel: identities and composites.

The unit of an adjunction F ⊣ G is a natural transformation Id_C ⇒ G∘F and the
counit is F∘G ⇒ Id_D, so the adjunction engine needs these functors as
`EnforcedFunctor`s.  Both subclasses only use the public `EnforcedFunctor`
hooks; the frozen Phase 0 interface is unchanged.
"""

from __future__ import annotations

from typing import Optional

from qbx.core.enforced_functor import Category, EnforcedFunctor, EnforcementMode


class IdentityFunctor(EnforcedFunctor):
    """Id_C: every object and morphism is sent to itself."""

    def __init__(self, category: Category, functor_id: Optional[str] = None,
                 mode: Optional[EnforcementMode] = None):
        fid = functor_id or f"Id[{category.id}]"
        super().__init__(fid, fid, category, category, mode=mode)
        for o in sorted(category.objects):
            self.map_object(o)
        for m in sorted(category.morphisms):
            self.map_morphism(m)

    def _map_object(self, obj_id: str) -> str:
        if obj_id not in self.source.objects:
            raise KeyError(obj_id)
        return obj_id

    def _map_morphism(self, morph_id: str) -> str:
        if morph_id not in self.source.morphisms:
            raise KeyError(morph_id)
        return morph_id


class ComposedFunctor(EnforcedFunctor):
    """The composite `second ∘ first` (apply `first`, then `second`).

    Requires `first.target is second.source`.  An object or morphism whose
    image under `first` is unknown, or whose image is not mapped by `second`,
    raises inside the hook, so `map_object` / `map_morphism` record a
    `*_map_error` violation instead of inventing an image.
    """

    def __init__(self, first: EnforcedFunctor, second: EnforcedFunctor,
                 functor_id: Optional[str] = None,
                 mode: Optional[EnforcementMode] = None):
        if first.target is not second.source:
            raise ValueError("ComposedFunctor needs first.target is second.source")
        fid = functor_id or f"{second.functor_id}∘{first.functor_id}"
        super().__init__(fid, fid, first.source, second.target,
                         mode=mode or first.mode)
        self.first, self.second = first, second
        for o in sorted(self.source.objects):
            self.map_object(o)
        for m in sorted(self.source.morphisms):
            self.map_morphism(m)

    def _map_object(self, obj_id: str) -> str:
        return self.second.object_map[self.first.object_map[obj_id]]

    def _map_morphism(self, morph_id: str) -> str:
        return self.second.morphism_map[self.first.morphism_map[morph_id]]
