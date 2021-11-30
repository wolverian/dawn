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
        defaultPackage = packages.wolverian-dawn;
        packages = {
          wolverian-dawn = pkgs.runCommand "wolverian-dawn"
            {
              buildInputs = [ pkgs.gnumake ];
            }
            ''
              ln -s ${./fonts} fonts
              ln -s ${./styles} styles
              ln -s ${./src} src
              ${pkgs.gnumake}/bin/make OUTPUT_DIR=$out
            '';
        };
        checks = {
          build = self.defaultPackage."${system}";
        };
      }
    );
}
