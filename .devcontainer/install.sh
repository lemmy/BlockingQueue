#!/bin/bash -i

## Fix issues with gitpod's stock .bashrc
cp /etc/skel/.bashrc $HOME

## Shorthands for git
git config --global alias.slog 'log --pretty=oneline --abbrev-commit'
git config --global alias.co checkout
git config --global alias.lco '!f() { git checkout ":/$1:" ; }; f'

## Waste less screen estate on the prompt.
echo 'export PS1="$ "' >> $HOME/.bashrc

## Make it easy to go back and forth in the (linear) git history.
echo 'function sn() { git log --reverse --pretty=%H main | grep -A 1 $(git rev-parse HEAD) | tail -n1 | xargs git show --color; }' >> $HOME/.bashrc
echo 'function n() { git reset --hard ; git log --reverse --pretty=%H main | grep -A 1 $(git rev-parse HEAD) | tail -n1 | xargs git checkout; }' >> $HOME/.bashrc
echo 'function p() { git checkout HEAD^; }' >> $HOME/.bashrc

## Place to install TLC, TLAPS, Apalache, ...
mkdir -p tools

## PATH below has two locations because of inconsistencies between Gitpod and Codespaces.
## Gitpod:     /workspace/...
## Codespaces: /workspaces/...

## Install TLA+ Tools
wget -qN https://nightly.tlapl.us/dist/tla2tools.jar -P tools/
echo "alias tlcrepl='java -cp /workspace/BlockingQueue/tools/tla2tools.jar:/workspaces/BlockingQueue/tools/tla2tools.jar tlc2.REPL'" >> $HOME/.bashrc
echo "alias tlc='java -cp /workspace/BlockingQueue/tools/tla2tools.jar:/workspaces/BlockingQueue/tools/tla2tools.jar tlc2.TLC'" >> $HOME/.bashrc

## Install CommunityModules
wget -qN https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar -P tools/

## Install TLAPS (proof system)
wget -N https://github.com/tlaplus/tlapm/releases/download/v1.4.5/tlaps-1.4.5-x86_64-linux-gnu-inst.bin -P /tmp
chmod +x /tmp/tlaps-1.4.5-x86_64-linux-gnu-inst.bin
/tmp/tlaps-1.4.5-x86_64-linux-gnu-inst.bin -d tools/tlaps
echo 'export PATH=$PATH:/workspace/BlockingQueue/tools/tlaps/bin:/workspaces/BlockingQueue/tools/tlaps/bin' >> $HOME/.bashrc

## Install Apalache
wget -qN https://github.com/informalsystems/apalache/releases/latest/download/apalache.tgz -P /tmp
mkdir -p tools/apalache
tar xvfz /tmp/apalache.tgz --directory tools/apalache/
echo 'export PATH=$PATH:/workspace/BlockingQueue/tools/apalache/bin:/workspaces/BlockingQueue/tools/apalache/bin' >> $HOME/.bashrc
tools/apalache/bin/apalache-mc config --enable-stats=true

## (Moved to the end to let it run in the background while we get started)
## - graphviz to visualize TLC's state graphs
## - htop to show system load
## - texlive-latex-recommended to generate pretty-printed specs
## - z3 for Apalache (comes with z3 turnkey) (TLAPS brings its own install)
## - r-base iff tutorial covers statistics (TODO)
sudo apt-get install -y graphviz htop
## No need because Apalache comes with z3 turnkey
#sudo apt-get install -y z3 libz3-java 
sudo apt-get install -y --no-install-recommends texlive-latex-recommended
#sudo apt-get install -y r-base

## Install TLA+ Toolbox
wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/TLAToolbox-1.8.0.deb -P /tmp
sudo dpkg -i /tmp/TLAToolbox-1.8.0.deb

## switch to first commit of the tutorial. Unshallow on Codespaces first.
if $(git rev-parse --is-shallow-repository); then git fetch --unshallow; fi
git co ':/v01'

## On Gitpod, open the readme.md file in the editor and move caret to line 11.
## Codespaces does not have an `open` command.
command -v open > /dev/null && open -g README.md:11

## Activate the aliases above. Unfortunately, source ~/.bashrc doesn't work this isn't an interactive shell. Thus, do it the hard way.
exec bash
