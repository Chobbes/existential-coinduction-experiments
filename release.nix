{ lib,
  nix-filter,
  mkCoqDerivation,
  version ? null,
  coq,
  dune_3,
  # All of these ocaml packages should probably come from the coq
  # version, or there will be disagreements between compiler versions.
  ocaml ? coq.ocaml,
  ITree,
  ... }:

{ existential-coinduction-experiments =
    mkCoqDerivation {
      namePrefix = [ "coq" ];
      pname = "existential-coinduction-experiments";
      owner = "existential-coinduction-experiments";

      inherit version;

      propagatedBuildInputs =
        [ coq
          dune_3
        ] ++
        # Coq libraries
        [ ITree
        ] ++
        # These ocaml packages have to come from coq.ocamlPackages to
        # avoid disagreements between ocaml compiler versions.
        [ ocaml
        ];

      src =
        # Some filtering to ignore files that are unimportant for the build.
        # Helps with caching and preventing rebuilds when, e.g., only
        # a README changed.
        nix-filter {
          root = ./.;
          include = [
            ./src
            ./src/Makefile
            (nix-filter.matchExt "v")
            (nix-filter.matchExt "ml")
            (nix-filter.matchExt "patch")
            (nix-filter.matchName "dune")
            (nix-filter.matchName "dune-project")
          ];

          exclude = [
            (nix-filter.matchExt "org")
            (nix-filter.matchExt "md")
            (nix-filter.matchExt "txt")
            (nix-filter.matchExt "yml")
            (nix-filter.matchName "README")
            ./.gitignore
          ];
        };

      buildPhase = ''
  make -C src/ extracted
  '';

      meta = {
        description = "Trying to do existential proofs with coinductive values";
        license = lib.licenses.mit;
      };
    };
}
