{
  description = "zettai_bootstrap";

  inputs = {
    nixpkgs.url = "nixpkgs/nixpkgs-unstable";
    utils.url = "github:numtide/flake-utils";
    starpath = {
      url = "github:mtoohey31/starpath?dir=nix";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        utils.follows = "utils";
      };
    };
  };

  outputs = { self, nixpkgs, utils, ... }@inputs: {
    overlays.default = final: _: {
      zettai_bootstrap = final.ocamlPackages.buildDunePackage rec {
        pname = "zettai_bootstrap";
        version = "0.1.0";

        minimalOcamlVersion = "4.14.1";
        duneVersion = "3";

        checkInputs = buildInputs ++ [ final.ocamlPackages.ppx_inline_test ];
        buildInputs = with final.ocamlPackages; [
          core
          ounit2
          ppx_deriving
          ppx_variants_conv
          starpath
        ];

        src = builtins.path { path = ./..; name = "zettai_bootstrap-src"; };
      };
    };
  } // utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs {
        overlays = [ inputs.starpath.overlays.default self.overlays.default ];
        inherit system;
      };
      inherit (pkgs) zettai_bootstrap mkShell ocamlformat ocamlPackages;
      inherit (ocamlPackages) bisect_ppx core dune_3 findlib ocaml ocaml-lsp
        ounit2 ppx_assert ppx_deriving ppx_inline_test ppx_variants_conv
        starpath;
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
          ounit2
          ppx_assert
          ppx_deriving
          ppx_inline_test
          ppx_variants_conv
          starpath
        ];
      };
    });
}
