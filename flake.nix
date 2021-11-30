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
        packages = flake-utils.lib.flattenTree {
          gnumake = pkgs.gnumake;
          agda = pkgs.agda;
        };
        defaultPackage = packages.gnumake;
        apps.gnumake = flake-utils.lib.mkApp
          {
            drv = packages.gnumake;
            name = "make";
          };
        defaultApp = apps.gnumake;
      }
    );
}
