## Delete all local tags when they are outdated.
```bash
git tag | xargs git tag -d
```

## Delete all remote tags.

```bash
$ git ls-remote --tags --refs origin | cut -f2 | xargs git push origin --delete
```

## Create a git tag for each commit in the current branch using the first list of the commit message.

git tag -f -a 'v00' f03ce46 -m "v00: IDE setup, nothing to see here."
```bash
IFS=$'\n'
for f in $(git log --pretty=oneline --abbrev-commit); do git tag -f -a $([[ ${f:8} =~ ((v[0-9]{2}) \((.[a-zA-Z]*)\)) ]] && echo ${BASH_REMATCH[2]}_${BASH_REMATCH[3]}) -m "${f:8}" ${f:0:7}; done
```

## Older variant that only used v?? as tag name
```bash
for f in $(git log --pretty=oneline --abbrev-commit); do git tag -f -a ${f:8:3} -m '${f:8}' ${f:0:7}; done
```

## Push newly created tags to remote git repository.

```bash
git push --follow-tags
```