# Non-reproducible "current" version:
with (import <nixpkgs> {});
# This works for RRN:
# with import (fetchTarball https://github.com/NixOS/nixpkgs-channels/archive/nixos-16.09.tar.gz) {};


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
                      libertine inconsolata # fonts for acmart in some configs
                      latexmk
                      lm
                      comment
                      algorithm2e
                      relsize
                      environ
                      trimspaces
                      ncctools
                      ncclatex
                      todonotes
                      totpages
                      stmaryrd lazylist polytable # for lhs2tex
                      xargs
                      biblatex
                      logreq
                      scheme-small wrapfig marvosym wasysym wasy cm-super unicode-math filehook lm-math capt-of
                      ucs
                      cmll
                      xstring ucharcat;
                  })
                ];
}
