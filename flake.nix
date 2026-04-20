{
  description = "Intrinsic Verification of Parsers and Formal Grammar Theory in Dependent Lambek Calculus (Agda + Lean implementations)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";

    # --- Agda side ------------------------------------------------------
    #
    # Track Agda itself and the Cubical Agda library the same way the
    # cubical-categorical-logic flake does: both are real flakes, and
    # `cubical` carries an overlay that exposes `agdaWithCubical`.
    agda.url = "github:agda/agda";
    cubical = {
      url = "github:agda/cubical";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-utils.follows = "flake-utils";
        agda.follows = "agda";
      };
    };

    # --- Lean side ------------------------------------------------------
    #
    # lean4-nix provides a Lean 4 + lake toolchain as a nixpkgs overlay,
    # honouring the version declared in `Lean/lean-toolchain`.
    lean4-nix = {
      url = "github:lenianiva/lean4-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    # Pin Mathlib and Canonical as flake inputs so their exact revisions
    # live in `flake.lock` alongside everything else. Lake still performs
    # the actual fetch via `lake-manifest.json`; these inputs are the
    # source of truth for which revision we expect, and make it trivial to
    # point the dev shell at a local checkout with `--override-input`.
    #
    # Keep the revs in sync with `Lean/lake-manifest.json`.
    mathlib = {
      url = "github:leanprover-community/mathlib4/308445d7985027f538e281e18df29ca16ede2ba3";
      flake = false;
    };
    canonical = {
      url = "github:chasenorman/CanonicalLean/062f62a0bc9aeb4fe9a747fdb7b1aa568d08596c";
      flake = false;
    };
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
    cubical,
    lean4-nix,
    mathlib,
    canonical,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        # On aarch64-darwin the binary Lean toolchain that lean4-nix
        # downloads ships dylibs whose Mach-O load commands have no
        # headerpad, so the default `fixDarwinDylibNames` setup-hook fails
        # with "larger updated load commands do not fit" when it tries to
        # rewrite rpaths in `libleanshared_1.dylib`. Strip that hook and
        # skip the fixup phase on the `lean-all` derivation; the Lean
        # binaries otherwise run fine out of the store.
        leanDylibFixupOverlay = final: prev: {
          lean =
            let
              fixedLeanAll = prev.lean.lean-all.overrideAttrs (old: {
                nativeBuildInputs = builtins.filter
                  (drv: (drv.pname or drv.name or "") != "fix-darwin-dylib-names-hook")
                  (old.nativeBuildInputs or [ ]);
                dontFixup = true;
              });
            in
            prev.lean // { lean-all = fixedLeanAll; };
        };

        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            cubical.inputs.agda.overlays.default
            cubical.overlays.default
            (lean4-nix.readToolchainFile ./Lean/lean-toolchain)
          ] ++ nixpkgs.lib.optional
            (system == "aarch64-darwin" || system == "x86_64-darwin")
            leanDylibFixupOverlay;
        };
      in
      {
        # `nix build` builds the Agda library, matching the
        # cubical-categorical-logic package. The Lean side is not built
        # here; use `lake build` inside the dev shell for that.
        packages.default = pkgs.agdaPackages.mkDerivation {
          pname = "grammars-and-semantic-actions";
          version = "0.1";

          src = pkgs.lib.cleanSourceWith {
            filter = name: _type:
              !(pkgs.lib.hasSuffix ".nix" name)
              && !(pkgs.lib.hasSuffix "flake.lock" name)
              && !(pkgs.lib.hasSuffix ".envrc" name);
            src = pkgs.lib.cleanSource ./src;
          };

          nativeBuildInputs = [ pkgs.ghc ];
          buildInputs = [ pkgs.cubical ];

          buildPhase = ''
            runHook preBuild
            runhaskell ./Everythings.hs gen-except
            agda -W error +RTS -M8G -RTS README.agda
            runHook postBuild
          '';

          meta = {
            description = "Cubical Agda formalisation of Dependent Lambek Calculus";
          };
        };

        # Development shell: pinned Agda + cubical library, pinned Lean +
        # lake, plus GHC and fix-whitespace for the Agda tooling. Activate
        # via `nix develop` or direnv.
        #
        # To use a local checkout of one of the dependencies, run e.g.:
        #   nix develop --override-input cubical path:../Cubical
        #   nix develop --override-input mathlib path:../mathlib4
        #   nix develop --override-input canonical path:../CanonicalLean
        #
        # The `mathlib` and `canonical` inputs are informational: lake
        # still fetches them according to `Lean/lake-manifest.json`. Their
        # presence here pins the expected revisions in `flake.lock`.
        devShells.default = pkgs.mkShell {
          nativeBuildInputs = [
            # Agda side
            pkgs.agdaWithCubical
            pkgs.ghc
            pkgs.haskellPackages.fix-whitespace

            # Lean side
            pkgs.lean.lean-all
          ];

          shellHook = ''
            echo "grammars-and-semantic-actions dev shell"
            echo "  agda:    $(agda --version 2>/dev/null | head -n1)"
            echo "  lean:    $(lean --version 2>/dev/null)"
            echo "  lake:    $(lake --version 2>/dev/null | head -n1)"
            echo
            echo "Pinned Lean dependencies (see flake.lock):"
            echo "  mathlib   → ${mathlib.rev}"
            echo "  canonical → ${canonical.rev}"
          '';
        };
      }
    );
}
