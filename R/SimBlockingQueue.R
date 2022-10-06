library(ggplot2)
library(plotly)

data <- read.csv(header = TRUE, sep = "#", file = "SimBlockingQueue.csv")
data <- unique(data)
data$procs <- data$producer + data$consumer
data$diff <- abs(data$producer - data$consumer)

############

data <- setNames(aggregate(x= data$level,
          by= list(data$bufCapacity, data$producer, data$consumer),
          FUN=min), c("bufCapacity", "producer", "consumer", "level"))

############

library("ggcorrplot")
my_data <- data[, c(1,2,3,4,5,6)]
corr <- round(cor(my_data), 1)
ggcorrplot(corr, p.mat = cor_pmat(my_data),
           hc.order = TRUE, type = "lower",
           color = c("#FC4E07", "white", "#00AFBB"),
           outline.col = "white", lab = TRUE)

############

data <- setNames(aggregate(x=data$level,
          by= list(data$bufCapacity, data$procs),
          FUN=min), c("bufCapacity", "procs", "level"))

plot_ly(
  x=data$bufCapacity,
  y=data$procs,
  z=data$level,
  color=data$diff,
  size=2,
  type="scatter3d",
  mode="markers" # markers, lines, surface, mesh3d
) %>%
  layout(scene = list(
    xaxis = list(title = "bufCapacity"), 
    yaxis = list(title = "|consumer \\cup producer|"),
    zaxis = list(title = "length")))

############

data <- setNames(aggregate(x= data$level,
                           by= list(data$bufCapacity),
                           FUN=min), c("bufCapacity", "level"))

plot_ly(
  x=data$bufCapacity,
  y=data$level,
  color=as.factor(data$diff),
  size=2,
  type="scatter",
  hoverinfo = 'x, y, color',
  mode="markers" # markers, lines, surface, mesh3d
) %>%
  layout(scene = list(
    xaxis = list(title = "bufCapacity"), 
    yaxis = list(title = "|consumer \\cup producer|")))

############

data$bufCapacity  <- as.factor(data$bufCapacity)
ggplot(data, aes(x=bufCapacity, y=level)) + 
  geom_violin()

############

data$x <- data$bufCapacity
data$y <- data$level
plot(data$x, data$y, pch=19, xlab='x', ylab='y')

#fit1 <- lm(y~x, data=data)
#fit2 <- lm(y~poly(x,2,raw=TRUE), data=data)
#fit3 <- lm(y~poly(x,3,raw=TRUE), data=data)
#fit4 <- lm(y~poly(x,4,raw=TRUE), data=data)
fit5 <- lm(y~poly(x,5,raw=TRUE), data=data)

x_axis <- seq(1, 15, length=15)

#add curve of each model to plot
#lines(x_axis, predict(fit1, data.frame(x=x_axis)), col='green')
#lines(x_axis, predict(fit2, data.frame(x=x_axis)), col='red')
#lines(x_axis, predict(fit3, data.frame(x=x_axis)), col='purple')
#lines(x_axis, predict(fit4, data.frame(x=x_axis)), col='blue')
lines(x_axis, predict(fit5, data.frame(x=x_axis)), col='orange')
