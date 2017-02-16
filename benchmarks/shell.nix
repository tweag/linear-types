with (import <nixpkgs> {});
let orgEmacs = emacsWithPackages (with emacsPackagesNg; [org]);
in stdenv.mkDerivation {
  name = "benchEnvs";
  buildInputs = [ pythonFull
                  pythonPackages.matplotlib
                  pythonPackages.numpy
                ];
}
