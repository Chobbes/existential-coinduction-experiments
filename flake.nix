{
  description = "Trying to do existential proofs with coinductive values";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/master";
    flake-utils.url = "github:numtide/flake-utils";
    nix-filter.url = "github:numtide/nix-filter";
  };

  outputs = { self, nixpkgs, flake-utils, nix-filter }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        lib = pkgs.lib;
        coq = pkgs.coq;
        ocamlPkgs = coq.ocamlPackages;
        coqPkgs = pkgs.coqPackages.overrideScope'
          (self: super:
            { ITree = super.ITree.overrideAttrs
                (s : rec
                  { version = "5.1.0";
                    name = "coq8.16-InteractionTrees-${version}";
                    src = fetchTarball {
                      # Version with rutt theory and mrec rutt theory.
                      url = "https://github.com/DeepSpec/InteractionTrees/archive/a1492ea5bcf9375414fcafec6b3d6a32d615ecd9.zip";
                      sha256 = "sha256:1spr98f5k9m3h16wjlajrs6w6gl0j6c39r1r2zi00n50aa5wqblz";
                    };
                    meta.broken = false;
                  });
            });

        version = "existential-coinduction-experiments:master";
      in rec {
        packages = {
          default = (pkgs.callPackage ./release.nix (ocamlPkgs // coqPkgs // { nix-filter = nix-filter.lib; inherit coq version; })).existential-coinduction-experiments;
        };

        app.default = flake-utils.lib.mkApp { drv = packages.default; };

        devShells = {
          default = pkgs.mkShell {
            inputsFrom = [ packages.default ];
          };
        };
      });
}
