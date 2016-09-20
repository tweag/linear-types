with (import <nixpkgs> {});
let orgEmacs = emacsWithPackages (with emacsPackagesNg; [org]);
in stdenv.mkDerivation {
  name = "docsEnv";
  buildInputs = [ # orgEmacs
                  biber
                  (texlive.combine {
                    inherit (texlive)
                      biblatex
                      logreq
                      scheme-small wrapfig marvosym wasysym wasy cm-super unicode-math filehook lm-math capt-of
                      xstring ucharcat;
                  })
                ];
}
