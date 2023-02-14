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
                  { version = "5.0.0";
                    name = "coq8.16-InteractionTrees-${version}";
                    src = fetchTarball {
                      # Version with rutt theory and mrec rutt theory.
                      url = "https://github.com/DeepSpec/InteractionTrees/archive/9c1637ea57d1afcef587eb438438c73247639c0e.zip";
                      sha256 = "sha256:0hcwplpaj2gx6c2abyp3w4g83hzvjnzfsh1sl9kfhd0r3pb9biar";
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
