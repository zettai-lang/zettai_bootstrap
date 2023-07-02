{
  description = "zettai_bootstrap";

  inputs = {
    nixpkgs.url = "nixpkgs/nixpkgs-unstable";
    utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, utils }: {
    overlays.default = final: _: {
      zettai_bootstrap = final.ocamlPackages.buildDunePackage rec {
        pname = "zettai_bootstrap";
        version = "0.1.0";

        minimalOcamlVersion = "4.14.1";
        duneVersion = "3";

        checkInputs = buildInputs ++ [ final.ocamlPackages.ppx_inline_test ];
        buildInputs = with final.ocamlPackages; [ core ppx_deriving ];

        src = builtins.path { path = ./.; name = "zettai_bootstrap-src"; };
      };
    };
  } // utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs {
        overlays = [ self.overlays.default ];
        inherit system;
      };
      inherit (pkgs) zettai_bootstrap mkShell ocamlformat ocamlPackages;
      inherit (ocamlPackages) bisect_ppx core dune_3 findlib ocaml ocaml-lsp
        ppx_deriving ppx_inline_test;
    in
    {
      packages.default = zettai_bootstrap;

      devShells.default = mkShell {
        packages = [
          bisect_ppx
          core
          dune_3
          findlib
          ocaml
          ocamlformat
          ocaml-lsp
          ppx_deriving
          ppx_inline_test
        ];
      };
    });
}
