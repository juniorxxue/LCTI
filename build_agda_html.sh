#!/bin/sh
ROOT_DIR=$(pwd)

build_agda_html() {
    local proof_dir=$1
    
    echo "Building HTML for $proof_dir..."
    
    # Generate Agda HTML
    cd $ROOT_DIR/$proof_dir/main_agda/ && agda --html --html-dir=$ROOT_DIR/src_htmls/$proof_dir --html-highlight=code Implicit/README.agda
    
    # Setup and build HTML generator
    # Remove existing agda directory if it exists to avoid moving source inside it
    rm -rf $ROOT_DIR/html_generator/src/agda
    mv $ROOT_DIR/src_htmls/$proof_dir $ROOT_DIR/html_generator/src/agda
    AGDA_PRJ_NAME=Implicit AGDA_PRJ_ROOT=README envsubst < $ROOT_DIR/html_generator/templates/src/_data/agdaModules.js > $ROOT_DIR/html_generator/src/_data/agdaModules.js
    cp $ROOT_DIR/html_generator/templates/src/agda/agda.11tydata.js $ROOT_DIR/html_generator/src/agda/
    
    # Build and cleanup
    cd $ROOT_DIR/html_generator && npm install && npm run build
    rm $ROOT_DIR/html_generator/src/_data/agdaModules.js
    rm -rf $ROOT_DIR/html_generator/src/agda
    
    # Remove existing html directory if it exists to avoid moving source inside it
    rm -rf $ROOT_DIR/$proof_dir/main_agda/html
    mv $ROOT_DIR/html_generator/_site/agda $ROOT_DIR/$proof_dir/main_agda/html
    
    echo "Completed building HTML for $proof_dir"
}

# Clean up and prepare
rm -rf $ROOT_DIR/src_htmls && mkdir -p $ROOT_DIR/src_htmls

# Build HTML for all proof directories
build_agda_html "proof_core"
build_agda_html "proof_core_top_bot"
build_agda_html "proof_variant_right2left"
