import Lake
open Lake DSL

package «HyperplaneTraversal» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «HyperplaneTraversal» where
  roots := #[`HyperplaneTraversal]
