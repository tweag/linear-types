with (import <nixpkgs> {});
let orgEmacs = emacsWithPackages (with emacsPackagesNg; [org]);
in stdenv.mkDerivation {
  name = "docsEnv";
  buildInputs = [ # orgEmacs
                  haskellPackages.lhs2tex
                  biber
                  (texlive.combine {
                    inherit (texlive)
                      # collection-fontutils
                      # tex-gyre tex-gyre-math
                      lm
                      todonotes
                      stmaryrd lazylist polytable # for lhs2tex
                      xargs
                      biblatex
                      logreq
                      scheme-small wrapfig marvosym wasysym wasy cm-super unicode-math filehook lm-math capt-of
                      xstring ucharcat cmll;
                  })
                ];
}
