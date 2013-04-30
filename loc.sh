#!/bin/sh

find -E . **/*.v | grep .v$ | xargs cat | wc -l 
