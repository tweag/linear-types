cd haskell
stack exec queue-exe -- --raw > tmp.json
cd ..
python analyze.py haskell/tmp.json
rm haskell/tmp.json
