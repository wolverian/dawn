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
          wolverian-dawn = pkgs.runCommand "make"
            {
              buildInputs = [ pkgs.agda pkgs.gnumake ];
            }
            ''
              $(pkgs.gnumake)/bin/make OUTPUT_DIR=$out
            '';
        };
        defaultPackage = packages.wolverian-dawn;
      }
    );
}
