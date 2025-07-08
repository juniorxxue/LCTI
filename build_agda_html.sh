#!/bin/sh
CURRENT_PATH=$(pwd)

rm -rf $CURRENT_PATH/src_htmls
mkdir -p $CURRENT_PATH/src_htmls
cd $CURRENT_PATH/proof_core/main_agda/ && agda --html --html-dir=$CURRENT_PATH/src_htmls/core --html-highlight=code Implicit/Paper.agda
# cd $CURRENT_PATH/proof_core_top_bot/main_agda/ && agda --html --html-dir=$CURRENT_PATH/src_htmls/core_top_bot --html-highlight=code Implicit/README.agda
# cd $CURRENT_PATH/proof_variant_right2left/main_agda/ && agda --html --html-dir=$CURRENT_PATH/src_htmls/variant_right2left --html-highlight=code Implicit/README.agda

mv $CURRENT_PATH/src_htmls/core $CURRENT_PATH/html_generator/src/agda
AGDA_PRJ_NAME=Implicit AGDA_PRJ_ROOT=Paper envsubst < $CURRENT_PATH/html_generator/templates/src/_data/agdaModules.js > $CURRENT_PATH/html_generator/src/_data/agdaModules.js
cp $CURRENT_PATH/html_generator/templates/src/agda/agda.11tydata.js $CURRENT_PATH/html_generator/src/agda/agda.11tydata.js
cd $CURRENT_PATH/html_generator && npm install && npm run build
rm -rf $CURRENT_PATH/html_generator/src/agda
mv $CURRENT_PATH/html_generator/_site/agda $CURRENT_PATH/proof_core/main_agda/html
