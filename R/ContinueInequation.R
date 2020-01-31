library(ggplot2)

data <- read.table(sep=",",header=T,text="vio,x,y
n, 1, 2
d, 1, 3
d, 1, 4
d, 1, 5
d, 1, 6
d, 1, 7
d, 1, 8
n, 2, 2
n, 2, 3
n, 2, 4
d, 2, 5
d, 2, 6
d, 2, 7
d, 2, 8
n, 3, 2
n, 3, 3
n, 3, 4
n, 3, 5
n, 3, 6
d, 3, 7
d, 3, 8")

ggplot(data, aes(x=x, y=y, shape=vio, group=vio)) +
  geom_point(size=3) +
  scale_shape_identity()+
  xlab("bufCapacity")+
  ylab("|producers \\cup consumers|")+
  annotate("segment", x = 1, xend = 3, y = 2.5, yend = 6.5,
           colour = "blue")+
  scale_x_continuous(breaks=c(1,2,3))
