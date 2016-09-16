with (import <nixpkgs> {});
let orgEmacs = emacsWithPackages (with emacsPackagesNg; [org]);
in stdenv.mkDerivation {
  name = "docsEnv";
  buildInputs = [ # orgEmacs
                  (texlive.combine {
                    inherit (texlive)
                      scheme-small wrapfig marvosym wasysym wasy cm-super unicode-math filehook lm-math;
                  })
                ];
}
