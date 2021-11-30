{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system};
      in
      rec {
        packages = {
          wolverian-dawn = pkgs.runCommand "wolverian-dawn"
            {
              buildInputs = [ pkgs.agda pkgs.gnumake ];
            }
            ''
              make OUTPUT_DIR=$out
            '';
        };
        defaultPackage = packages.wolverian-dawn;
      }
    );
}
