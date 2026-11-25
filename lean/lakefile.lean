import Lake
open Lake DSL

package «HyperplaneTraversal» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]
  moreLeanArgs := #["-j", "1"]

@[default_target]
lean_lib «HyperplaneTraversal» where
  roots := #[`HyperplaneTraversal]
