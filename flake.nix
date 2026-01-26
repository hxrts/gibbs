{
  description = "Gibbs - Mean-field theory meets multiparty session types";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };

        nativeBuildInputs = with pkgs; [
          just
          coreutils
          findutils
          gawk
          gnused
          elan
        ];

        buildInputs =
          with pkgs;
          lib.optionals stdenv.isDarwin [
            libiconv
          ];

      in
      {
        devShells.default = pkgs.mkShell {
          inherit nativeBuildInputs buildInputs;

          shellHook = ''
            echo "Gibbs development environment"
            echo "Lean: $(elan show 2>/dev/null | head -1 || echo 'not configured')"
          '';
        };
      }
    );
}
