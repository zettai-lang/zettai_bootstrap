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

  outputs = { self, nixpkgs, utils, starpath }: {
    overlays = rec {
      expects-starpath = final: _: {
        zettai_bootstrap = final.callPackage
          ({ ocamlPackages }:
            ocamlPackages.buildDunePackage {
              pname = "zettai_bootstrap";
              version = "0.1.0";

              minimalOcamlVersion = "4.14.1";
              duneVersion = "3";

              doCheck = true;
              buildInputs = with ocamlPackages; [
                ounit2
                ppx_assert
                ppx_deriving
                ppx_expect
                ppx_variants_conv
                ocamlPackages.starpath
              ];

              src = builtins.path { path = ./..; name = "zettai_bootstrap-src"; };
            })
          { };
      };
      default = nixpkgs.lib.composeManyExtensions [
        starpath.overlays.default
        expects-starpath
      ];
    };
  } // utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs {
        overlays = [ self.overlays.default ];
        inherit system;
      };
      inherit (pkgs) mkShell ocamlformat ocamlPackages zettai_bootstrap;
      inherit (ocamlPackages) bisect_ppx ocaml-lsp;
    in
    {
      packages.default = zettai_bootstrap;

      devShells.default = mkShell {
        inputsFrom = [ zettai_bootstrap ];
        packages = [ bisect_ppx ocamlformat ocaml-lsp ];
      };
    });
}
